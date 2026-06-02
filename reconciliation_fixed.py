"""
Account Reconciliation Tool
- Load large Excel/CSV files (5L+ rows)
- View, Edit, Add, Delete rows
- Triple simultaneous column filter
- Alternating Reconciliation:
    * Sort by date
    * Check first entry — Debit or Credit
    * If Debit first  → find next Credit(s) whose SUM == that Debit amount
    * If Credit first → find next Debit(s)  whose SUM == that Credit amount
    * After each match, flip side and repeat from next unmatched entry
    * Number of entries in a combination is unknown / variable
- Reconcile at All OP Data + Expense Type level separately
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import pandas as pd
import numpy as np
from datetime import datetime, timedelta
import threading
import os
import time
from itertools import combinations

# ─────────────────────────────────────────────
# CONFIG — column name mappings (edit if needed)
# ─────────────────────────────────────────────
COL_DATE      = "Post Date"
COL_DEBIT     = "Debit"
COL_CREDIT    = "Credit"
COL_OP_DATA   = "All OP Data"
COL_EXP_TYPE  = "Expense Type"
COL_NAME      = "Name"

# Expense types that must ONLY reconcile within the same type (strict 1-to-1 category)
STRICT_EXPENSE_TYPES = {"fuel", "insurance", "camera", "prepass", "plates"}

PAGE_SIZE = 500



# ══════════════════════════════════════════════════════════
#  RECONCILIATION ENGINE  (optimised — array-based, int math)
#  Phase 1:   Exact 1:1 matching (debit == credit)
#  Phase 1.5: Consecutive N:1 sum matching (multi-pass)
#  Phase 1.6: Greedy accumulation (all-remaining → single target)
#  Phase 1.7: N:M consecutive matching (window vs window)
#  Phase 2A:  Meet-in-the-middle subset-sum (≤25 entries, any combo)
#  Phase 2B:  Combinatorial fallback (larger groups, combo ≤5)
# ══════════════════════════════════════════════════════════



def reconcile_group(group_df: pd.DataFrame, match_counter_start: int = 1):
    """
    Reconcile a single group using multi-phase matching.

    Phase 1:   Exact 1:1 — debit == credit (across entire group)
    Phase 1.5: Consecutive sum — contiguous sequence of entries on
               one side sums to a single entry on the opposite side

    Returns (df, next_match_counter).
    """
    GROUP_TIME_LIMIT = 30.0  # hard cap: 30 seconds per group
    _group_start = time.perf_counter()

    def _group_timed_out():
        return (time.perf_counter() - _group_start) > GROUP_TIME_LIMIT

    df = group_df.copy().reset_index(drop=True)
    df[COL_DATE] = pd.to_datetime(df[COL_DATE], errors="coerce")
    df = df.sort_values([COL_DATE], kind="mergesort").reset_index(drop=True)

    n = len(df)

    # ── Vectorised pre-extraction ──
    debit_arr  = [0] * n
    credit_arr = [0] * n

    if COL_DEBIT in df.columns:
        dvals = pd.to_numeric(df[COL_DEBIT], errors="coerce").fillna(0.0).values
        for i in range(n):
            if dvals[i] != 0.0:
                debit_arr[i] = int(round(dvals[i] * 100))

    if COL_CREDIT in df.columns:
        cvals = pd.to_numeric(df[COL_CREDIT], errors="coerce").fillna(0.0).values
        for i in range(n):
            if cvals[i] != 0.0:
                credit_arr[i] = int(round(cvals[i] * 100))

    # Result arrays
    matched    = [False] * n
    match_id   = [""] * n
    match_note = [""] * n
    match_type = [""] * n      # "exact" for 1:1, "consecutive" for consecutive-sum
    used       = [False] * n
    match_counter = match_counter_start

    # ──────────────────────────────────────────────────────────────────
    # PHASE 1: Exact 1:1 matches (debit value == credit value)
    # Build a map of credit values → list of indices for O(1) lookup
    # ──────────────────────────────────────────────────────────────────
    credit_map = {}  # paise_value → [list of indices]
    for i in range(n):
        if credit_arr[i] != 0:
            credit_map.setdefault(credit_arr[i], []).append(i)

    for i in range(n):
        if used[i] or debit_arr[i] == 0:
            continue
        d_val = debit_arr[i]
        if d_val in credit_map:
            # Find first unused credit with this value
            clist = credit_map[d_val]
            for ci in clist:
                if not used[ci]:
                    # 1:1 match found
                    mid = f"M{match_counter:04d}"
                    match_counter += 1
                    amount = d_val / 100.0
                    note = f"Debit ₹{amount:,.2f} ↔ Credit ₹{amount:,.2f} (1:1)"

                    for idx in [i, ci]:
                        matched[idx]    = True
                        match_id[idx]   = mid
                        match_note[idx] = note
                        match_type[idx] = "exact"
                        used[idx]       = True
                    break

    # ──────────────────────────────────────────────────────────────────
    # PHASE 1.5: CONSECUTIVE SUM MATCHING  (multi-pass until stable)
    #   Find contiguous/consecutive sequences of debit entries whose
    #   sum equals a single credit entry, and vice versa.
    #   Runs repeatedly: after each round of matches, newly-adjacent
    #   entries may form new consecutive windows.
    # ──────────────────────────────────────────────────────────────────

    def _find_consecutive_sum_matches(source_arr, target_arr, source_label, target_label):
        """Find consecutive sequences in source_arr that sum to a target in target_arr.
        Returns number of new matches found (0 means done).
        """
        nonlocal match_counter
        matches_found = 0

        # Collect unused source indices (in order)
        src_indices = [i for i in range(n) if source_arr[i] != 0 and not used[i]]
        if not src_indices:
            return 0

        # Collect unused target values → indices for lookup
        tgt_map = {}  # paise_value → [list of indices]
        for i in range(n):
            if target_arr[i] != 0 and not used[i]:
                tgt_map.setdefault(target_arr[i], []).append(i)
        if not tgt_map:
            return 0

        for l in range(len(src_indices)):
            if used[src_indices[l]]:
                continue
            if _group_timed_out():
                return matches_found
            running_sum = 0
            for r in range(l, len(src_indices)):
                if r > l:
                    gap_has_source = False
                    for g in range(src_indices[r-1] + 1, src_indices[r]):
                        if source_arr[g] != 0 and not used[g]:
                            gap_has_source = True
                            break
                    if gap_has_source:
                        break

                idx_r = src_indices[r]
                if used[idx_r]:
                    break
                running_sum += source_arr[idx_r]
                count = r - l + 1

                if count < 2:
                    continue

                if running_sum in tgt_map:
                    tgt_list = tgt_map[running_sum]
                    matched_tgt = None
                    for ti in tgt_list:
                        if not used[ti]:
                            matched_tgt = ti
                            break
                    if matched_tgt is not None:
                        mid = f"M{match_counter:04d}"
                        match_counter += 1
                        amount = running_sum / 100.0
                        consec_indices = [src_indices[k] for k in range(l, r + 1)]
                        note = (f"{count} consecutive {source_label} entries "
                                f"₹{amount:,.2f} ↔ {target_label} ₹{amount:,.2f} "
                                f"(consecutive sum)")

                        all_indices = consec_indices + [matched_tgt]
                        for idx in all_indices:
                            matched[idx]    = True
                            match_id[idx]   = mid
                            match_note[idx] = note
                            match_type[idx] = "consecutive"
                            used[idx]       = True

                        tgt_list.remove(matched_tgt)
                        if not tgt_list:
                            del tgt_map[running_sum]

                        matches_found += 1
                        break
        return matches_found

    # Run consecutive N:1 matching in multiple passes until stable
    for _pass in range(20):
        if _group_timed_out():
            break
        found = 0
        found += _find_consecutive_sum_matches(debit_arr, credit_arr, "debit", "Credit")
        found += _find_consecutive_sum_matches(credit_arr, debit_arr, "credit", "Debit")
        if found == 0:
            break

    # ──────────────────────────────────────────────────────────────────
    # PHASE 1.6: GREEDY ACCUMULATION  (all-remaining → single target)
    #   For each unmatched entry on one side, check if ALL remaining
    #   unmatched entries on the other side sum to it.  Catches large
    #   N:1 patterns (e.g. 14 debits → 1 credit) in O(n).
    # ──────────────────────────────────────────────────────────────────

    def _greedy_all_remaining(source_arr, target_arr, source_label, target_label):
        """Check if all remaining unused source entries sum to a single target."""
        nonlocal match_counter
        matches_found = 0

        src_indices = [i for i in range(n) if source_arr[i] != 0 and not used[i]]
        if len(src_indices) < 2:
            return 0
        src_total = sum(source_arr[i] for i in src_indices)

        for i in range(n):
            if target_arr[i] != 0 and not used[i] and target_arr[i] == src_total:
                mid = f"M{match_counter:04d}"
                match_counter += 1
                amount = src_total / 100.0
                note = (f"{len(src_indices)} {source_label} entries "
                        f"₹{amount:,.2f} ↔ {target_label} ₹{amount:,.2f} "
                        f"(sum match)")
                all_matched = src_indices + [i]
                for idx in all_matched:
                    matched[idx]    = True
                    match_id[idx]   = mid
                    match_note[idx] = note
                    match_type[idx] = "sum"
                    used[idx]       = True
                matches_found += 1
                break  # all source entries are now used
        return matches_found

    for _pass in range(10):
        if _group_timed_out():
            break
        found = 0
        found += _greedy_all_remaining(debit_arr, credit_arr, "debit", "Credit")
        found += _greedy_all_remaining(credit_arr, debit_arr, "credit", "Debit")
        if found == 0:
            break

    # ──────────────────────────────────────────────────────────────────
    # PHASE 1.7: N:M CONSECUTIVE MATCHING
    #   Contiguous window of debits whose sum == contiguous window of
    #   credits.  Both windows must have ≥ 2 entries (N:1 already done).
    # ──────────────────────────────────────────────────────────────────

    MAX_WINDOWS = 50_000  # cap to prevent memory/time blowup

    def _get_consecutive_windows(arr, min_size=1, max_size=15):
        """Return list of (indices_list, window_sum) for consecutive unused entries."""
        windows = []
        idxs = [i for i in range(n) if arr[i] != 0 and not used[i]]
        if len(idxs) < min_size:
            return windows
        for l in range(len(idxs)):
            if _group_timed_out() or len(windows) >= MAX_WINDOWS:
                break
            if used[idxs[l]]:
                continue
            running = 0
            for r in range(l, min(l + max_size, len(idxs))):
                if r > l:
                    gap = False
                    for g in range(idxs[r-1] + 1, idxs[r]):
                        if arr[g] != 0 and not used[g]:
                            gap = True
                            break
                    if gap:
                        break
                if used[idxs[r]]:
                    break
                running += arr[idxs[r]]
                sz = r - l + 1
                if sz >= min_size:
                    windows.append(([idxs[k] for k in range(l, r + 1)], running))
        return windows

    # Build debit and credit windows, match by sum
    if not _group_timed_out():
        d_windows = _get_consecutive_windows(debit_arr, min_size=2, max_size=10)
        c_win_map = {}  # sum → list of index-lists
        for c_idx_list, c_sum in _get_consecutive_windows(credit_arr, min_size=2, max_size=10):
            c_win_map.setdefault(c_sum, []).append(c_idx_list)

        for d_idx_list, d_sum in d_windows:
            if _group_timed_out():
                break
            if any(used[i] for i in d_idx_list):
                continue
            if d_sum not in c_win_map:
                continue
            for c_idx_list in c_win_map[d_sum]:
                if any(used[i] for i in c_idx_list):
                    continue
                # N:M match found
                mid = f"M{match_counter:04d}"
                match_counter += 1
                amount = d_sum / 100.0
                note = (f"{len(d_idx_list)} debit + {len(c_idx_list)} credit entries "
                        f"₹{amount:,.2f} (N:M consecutive)")
                for idx in d_idx_list + c_idx_list:
                    matched[idx]    = True
                    match_id[idx]   = mid
                    match_note[idx] = note
                    match_type[idx] = "consecutive"
                    used[idx]       = True
                break

    # ──────────────────────────────────────────────────────────────────
    # PHASE 2: GLOBAL (NON-CONSECUTIVE) SUM MATCHING
    #   Strategy A — Meet-in-the-middle subset-sum for ≤ MITM_MAX
    #     source entries: O(2^(n/2)), finds ANY subset that sums to
    #     a target.  Handles 6–25 entry combos that combinatorial
    #     approach cannot reach.
    #   Strategy B — Combinatorial fallback for larger groups.
    # ──────────────────────────────────────────────────────────────────

    MITM_MAX = 25              # max source entries for meet-in-the-middle
    MAX_COMBO = 5              # fallback combo size for large groups
    MAX_SRC_BIG = 80
    MAX_ITERATIONS = 500_000
    TIME_LIMIT = 10.0

    _phase2_start = time.perf_counter()  # separate timer for Phase 2

    # ── Strategy A: Meet-in-the-middle subset-sum ─────────────────────

    MITM_TIME_LIMIT = 5.0   # seconds per MITM call

    def _mitm_find_subset(entries, target):
        """Find a subset (size ≥ 2) of entries that sums exactly to target.
        entries: list of (index, value).  Returns list of indices or None.
        Uses meet-in-the-middle: O(2^(n/2)) time and space.
        """
        ne = len(entries)
        if ne < 2:
            return None
        _mitm_start = time.perf_counter()
        mid_pt = ne // 2
        left, right = entries[:mid_pt], entries[mid_pt:]

        # All non-empty subsets of left half → {sum: (indices, count)}
        left_sums = {}  # sum → (indices_list, subset_size)
        for mask in range(1, 1 << len(left)):
            if mask % 10_000 == 0 and (time.perf_counter() - _mitm_start) > MITM_TIME_LIMIT:
                return None  # bail out
            s, idxs = 0, []
            for i in range(len(left)):
                if mask & (1 << i):
                    s += left[i][1]
                    idxs.append(left[i][0])
            if s <= target and s not in left_sums:
                left_sums[s] = idxs

        # Left-only hit
        if target in left_sums and len(left_sums[target]) >= 2:
            return left_sums[target]

        # Right subsets, check complement in left
        for mask in range(1, 1 << len(right)):
            if mask % 10_000 == 0 and (time.perf_counter() - _mitm_start) > MITM_TIME_LIMIT:
                return None  # bail out
            s, idxs = 0, []
            for i in range(len(right)):
                if mask & (1 << i):
                    s += right[i][1]
                    idxs.append(right[i][0])
            if s > target:
                continue
            if s == target and len(idxs) >= 2:
                return idxs
            complement = target - s
            if complement in left_sums:
                combined = left_sums[complement] + idxs
                if len(combined) >= 2:
                    return combined
        return None

    def _find_global_mitm(source_arr, target_arr, source_label, target_label):
        """Meet-in-the-middle global sum matching for small groups."""
        nonlocal match_counter
        src = [(i, source_arr[i]) for i in range(n)
               if source_arr[i] != 0 and not used[i]]
        if len(src) < 2 or len(src) > MITM_MAX:
            return False

        targets = [(i, target_arr[i]) for i in range(n)
                   if target_arr[i] != 0 and not used[i]]
        if not targets:
            return False

        found_any = False
        for tgt_idx, tgt_val in targets:
            if used[tgt_idx]:
                continue
            src = [(i, v) for i, v in src if not used[i]]
            if len(src) < 2:
                break
            result = _mitm_find_subset(src, tgt_val)
            if result is not None:
                mid = f"M{match_counter:04d}"
                match_counter += 1
                amount = tgt_val / 100.0
                note = (f"{len(result)} {source_label} entries "
                        f"₹{amount:,.2f} ↔ {target_label} ₹{amount:,.2f} "
                        f"(sum match)")
                for idx in result + [tgt_idx]:
                    matched[idx]    = True
                    match_id[idx]   = mid
                    match_note[idx] = note
                    match_type[idx] = "sum"
                    used[idx]       = True
                found_any = True
        return found_any

    # Run MITM in passes until stable
    for _mitm_pass in range(10):
        if _group_timed_out():
            break
        found_mitm = False
        d_rem = sum(1 for i in range(n) if debit_arr[i] != 0 and not used[i])
        c_rem = sum(1 for i in range(n) if credit_arr[i] != 0 and not used[i])
        if 2 <= d_rem <= MITM_MAX:
            found_mitm |= _find_global_mitm(debit_arr, credit_arr, "debit", "Credit")
        if 2 <= c_rem <= MITM_MAX:
            found_mitm |= _find_global_mitm(credit_arr, debit_arr, "credit", "Debit")
        if not found_mitm:
            break

    # ── Strategy B: Combinatorial fallback for remaining/larger groups ─

    def _find_global_sum_matches(source_arr, target_arr, source_label, target_label):
        nonlocal match_counter
        if _group_timed_out():
            return
        _phase2b_start = time.perf_counter()  # own timer for this call
        src = [(i, source_arr[i]) for i in range(n) if source_arr[i] != 0 and not used[i]]
        if len(src) < 2:
            return

        tgt_map = {}
        for i in range(n):
            if target_arr[i] != 0 and not used[i]:
                tgt_map.setdefault(target_arr[i], []).append(i)
        if not tgt_map:
            return

        effective_max = MAX_COMBO
        if len(src) > MAX_SRC_BIG:
            effective_max = min(effective_max, 3)

        iteration_count = 0

        for combo_size in range(2, effective_max + 1):
            src = [(i, v) for i, v in src if not used[i]]
            if len(src) < combo_size:
                break

            for combo in combinations(src, combo_size):
                iteration_count += 1
                if iteration_count > MAX_ITERATIONS:
                    return
                if iteration_count % 10_000 == 0:
                    if time.perf_counter() - _phase2b_start > TIME_LIMIT:
                        return
                    if _group_timed_out():
                        return

                if any(used[idx] for idx, _ in combo):
                    continue
                total = sum(v for _, v in combo)
                if total not in tgt_map:
                    continue
                tgt_list = tgt_map[total]
                matched_tgt = None
                for ti in tgt_list:
                    if not used[ti]:
                        matched_tgt = ti
                        break
                if matched_tgt is None:
                    continue

                mid = f"M{match_counter:04d}"
                match_counter += 1
                amount = total / 100.0
                combo_indices = [idx for idx, _ in combo]
                note = (f"{combo_size} {source_label} entries "
                        f"₹{amount:,.2f} ↔ {target_label} ₹{amount:,.2f} "
                        f"(sum match)")

                for idx in combo_indices + [matched_tgt]:
                    matched[idx]    = True
                    match_id[idx]   = mid
                    match_note[idx] = note
                    match_type[idx] = "sum"
                    used[idx]       = True

                tgt_list.remove(matched_tgt)
                if not tgt_list:
                    del tgt_map[total]

    if not _group_timed_out():
        _find_global_sum_matches(debit_arr, credit_arr, "debit", "Credit")
    if not _group_timed_out():
        _find_global_sum_matches(credit_arr, debit_arr, "credit", "Debit")

    # Write results back in bulk
    df["_matched"]    = matched
    df["_match_id"]   = match_id
    df["_match_note"] = match_note
    df["_match_type"] = match_type

    # Assign status
    statuses = []
    for i in range(n):
        if matched[i] and match_type[i] == "sum":
            statuses.append("🧮 Sum Match")
        elif matched[i] and match_type[i] == "consecutive":
            statuses.append("📊 Consecutive Match")
        elif matched[i]:
            statuses.append("✅ Matched")
        else:
            statuses.append("❌ Unmatched")
    df["_status"] = statuses
    return df, match_counter


def _row_group_key(row, has_op_data: bool, has_name: bool, has_exp_type: bool) -> tuple:
    """
    Build a (entity_key, expense_group) tuple for a row.

    Entity key priority:
      1. All OP Data  (if non-blank)
      2. Name         (fallback when All OP Data is blank/null)
      3. '__unknown__'

    Expense group:
      - Strict types (fuel, insurance, camera, prepass, plates) → exact type name
      - All other types → '__other__'  (can cross-match freely)
    """
    # ── Entity ──────────────────────────────────────────────────────────────
    entity = "__unknown__"
    if has_op_data:
        op = row[COL_OP_DATA]
        if pd.notna(op) and str(op).strip() not in ("", "nan"):
            entity = str(op).strip().lower()
    if entity == "__unknown__" and has_name:
        nm = row[COL_NAME]
        if pd.notna(nm) and str(nm).strip() not in ("", "nan"):
            entity = str(nm).strip().lower()

    # ── Expense group ────────────────────────────────────────────────────────
    exp_group = "__other__"
    if has_exp_type:
        raw = row[COL_EXP_TYPE]
        exp = str(raw).strip().lower() if pd.notna(raw) and str(raw).strip() not in ("", "nan") else ""
        if exp in STRICT_EXPENSE_TYPES:
            exp_group = exp          # strict: keep exact type so they never cross-match
        # else: leave as '__other__' — all non-strict types pool together

    return (entity, exp_group)


def run_reconciliation(df: pd.DataFrame, progress_cb=None) -> pd.DataFrame:
    """
    New grouping logic:
      • Entity = All OP Data  (primary)  →  Name  (fallback if OP Data is blank)
      • Expense group:
          - fuel / insurance / camera / prepass / plates  →  strict (same-type only)
          - everything else (advance, repair, eps, paycheck, void, …)  → '__other__'
            these pool together and can cross-match freely within the same entity

    progress_cb: optional callable(msg: str) for UI progress updates.
    """
    has_op_data  = COL_OP_DATA  in df.columns
    has_name     = COL_NAME     in df.columns
    has_exp_type = COL_EXP_TYPE in df.columns

    if not has_op_data and not has_name:
        if progress_cb:
            progress_cb("Reconciling (single group)…")
        result, _ = reconcile_group(df)
        return result

    df = df.copy()

    # ── Vectorised group-key construction (replaces slow df.apply) ────────
    # Entity: primary = All OP Data, fallback = Name
    entity = pd.Series("__unknown__", index=df.index)
    if has_op_data:
        op = df[COL_OP_DATA].fillna("").astype(str).str.strip().str.lower()
        mask_op = ~op.isin(["", "nan"])
        entity = entity.where(~mask_op, op)
    if has_name:
        nm = df[COL_NAME].fillna("").astype(str).str.strip().str.lower()
        mask_nm = (entity == "__unknown__") & ~nm.isin(["", "nan"])
        entity = entity.where(~mask_nm, nm)

    # Expense group: strict types stay as-is, everything else → '__other__'
    exp_group = pd.Series("__other__", index=df.index)
    if has_exp_type:
        exp_raw = df[COL_EXP_TYPE].fillna("").astype(str).str.strip().str.lower()
        is_strict = exp_raw.isin(STRICT_EXPENSE_TYPES)
        exp_group = exp_group.where(~is_strict, exp_raw)

    df["_grp"] = list(zip(entity, exp_group))

    groups = list(df.groupby("_grp", dropna=False, sort=False))
    total_groups = len(groups)
    results = []
    global_counter = 1
    failed_groups = 0
    for idx, (_key, grp) in enumerate(groups, 1):
        if progress_cb and (idx % 5 == 0 or idx == 1):
            progress_cb(f"Processing group {idx}/{total_groups} ({len(grp)} rows)…")
        try:
            reconciled, global_counter = reconcile_group(
                grp.drop(columns=["_grp"]), match_counter_start=global_counter
            )
            results.append(reconciled)
        except Exception:
            # If a single group fails, keep its rows unmatched rather than
            # crashing the entire reconciliation.
            failed_grp = grp.drop(columns=["_grp"]).copy()
            failed_grp["_matched"]    = False
            failed_grp["_match_id"]   = ""
            failed_grp["_match_note"] = ""
            failed_grp["_match_type"] = ""
            failed_grp["_status"]     = "❌ Unmatched"
            results.append(failed_grp)
            failed_groups += 1

    result = pd.concat(results, ignore_index=True)

    if progress_cb and failed_groups > 0:
        progress_cb(f"⚠ {failed_groups} group(s) could not be reconciled — marked Unmatched")

    # ── POST-PROCESS: relabel cross-type matches as CM001, CM002, … ──────
    if has_exp_type and COL_EXP_TYPE in result.columns:
        if progress_cb:
            progress_cb("Detecting cross-type matches…")
        cm_counter = 1
        # Vectorised: group by match_id quickly
        matched_mask = result["_match_id"] != ""
        if matched_mask.any():
            id_groups = result.loc[matched_mask].groupby("_match_id", sort=False)
            for mid, grp_rows in id_groups:
                exp_types = set(
                    str(t).strip().lower()
                    for t in grp_rows[COL_EXP_TYPE].dropna()
                    if str(t).strip().lower() not in ("", "nan")
                )
                if len(exp_types) > 1:
                    mask = result["_match_id"] == mid
                    new_id = f"CM{cm_counter:03d}"
                    cm_counter += 1
                    cross_types = ", ".join(sorted(exp_types))
                    old_note = grp_rows["_match_note"].iloc[0] if "_match_note" in grp_rows.columns else ""
                    new_note = f"{old_note} [Cross: {cross_types}]"
                    result.loc[mask, "_match_id"]   = new_id
                    result.loc[mask, "_match_note"] = new_note
                    result.loc[mask, "_status"]     = "🔄 Cross Matched"

    return result


# ══════════════════════════════════════════════════════════
#  MAIN APPLICATION
# ══════════════════════════════════════════════════════════

class ReconciliationApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Account Reconciliation Tool")
        self.geometry("1500x850")
        self.configure(bg="#1a1a2e")

        self.df_original  = None
        self.df_display   = None
        self.current_page = 0
        self.total_pages  = 0
        self.file_path    = ""
        self.hidden_columns = set()   # columns hidden from view (not deleted)
        self.auto_save_path = ""      # path for live auto-save
        self._auto_save_lock = threading.Lock()  # prevent overlapping saves

        self._build_ui()
        self._apply_styles()

    # ── UI CONSTRUCTION ──────────────────────────────────

    def _build_ui(self):
        # ── TOP BAR ──
        top = tk.Frame(self, bg="#16213e", pady=10)
        top.pack(fill="x")

        tk.Label(
            top, text="⚖  Account Reconciliation",
            font=("Segoe UI", 15, "bold"),
            fg="#e94560", bg="#16213e"
        ).pack(side="left", padx=16)

        self.lbl_file = tk.Label(
            top, text="No file loaded",
            fg="#a8b2d8", bg="#16213e",
            font=("Segoe UI", 9)
        )
        self.lbl_file.pack(side="right", padx=16)

        # ── Auto-save status indicator ──
        self.lbl_autosave = tk.Label(
            top, text="",
            fg="#4ade80", bg="#16213e",
            font=("Segoe UI", 8)
        )
        self.lbl_autosave.pack(side="right", padx=8)

        # ── BUTTON ROW 1 ──
        btn_row1 = tk.Frame(self, bg="#16213e", pady=4)
        btn_row1.pack(fill="x", padx=8)

        self._make_btn(btn_row1, "📂  Browse & Load File",  self.load_file,        "#e94560").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row1, "⚡  Run Reconciliation",  self.run_recon,         "#e94560").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row1, "💾  Export Results",       self.export,            "#e94560").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row1, "+ Insert Above",          lambda: self.add_row("above"), "#e94560").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row1, "+ Insert Below",          lambda: self.add_row("below"), "#e94560").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row1, "🗑  Delete Row",           self.delete_row,        "#c0392b").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row1, "✏  Edit Cell",            self.edit_cell,         "#533483").pack(side="left", padx=4, pady=2)

        # ── BUTTON ROW 2 ──
        btn_row2 = tk.Frame(self, bg="#16213e", pady=4)
        btn_row2.pack(fill="x", padx=8)

        self._make_btn(btn_row2, "⚡  Bulk Edit Column",    self.bulk_edit,         "#0f6e56").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row2, "🔗  Show Match",          self.show_match,        "#b8860b").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row2, "➕  Add Column",          self.add_column,        "#7b2d8e").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row2, "👁  Hide/Show Columns",   self.hide_show_columns, "#2c6e49").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row2, "🗑  Delete Column",       self.delete_columns,    "#8b1a1a").pack(side="left", padx=4, pady=2)
        self._make_btn(btn_row2, "🔄  Auto-Save Path",      self.set_auto_save_path,"#0a7e3d").pack(side="left", padx=4, pady=2)

        # ── FILTER BAR (TRIPLE) ──
        fbar = tk.Frame(self, bg="#0f3460", pady=8)
        fbar.pack(fill="x", padx=0)

        tk.Label(fbar, text="  Filters:", fg="white", bg="#0f3460",
                 font=("Segoe UI", 10, "bold")).grid(row=0, column=0, rowspan=3, padx=(10,6), sticky="ns")

        # Three filter rows
        self.filter_cols   = []
        self.filter_vals   = []
        self.filter_enabled = []
        self.filter_blanks = []   # BooleanVar per filter row

        filter_labels = ["Filter 1:", "Filter 2:", "Filter 3:"]
        for i in range(3):
            row_frame = tk.Frame(fbar, bg="#0f3460")
            row_frame.grid(row=i, column=1, sticky="w", pady=2, padx=4)

            tk.Label(row_frame, text=filter_labels[i], fg="#a8b2d8", bg="#0f3460",
                     font=("Segoe UI", 9), width=7, anchor="e").pack(side="left")

            col_cb = ttk.Combobox(row_frame, width=16, state="readonly",
                                  font=("Segoe UI", 9))
            col_cb.pack(side="left", padx=(4, 4))
            self.filter_cols.append(col_cb)

            val_entry = tk.Entry(row_frame, width=20, bg="#1a1a2e", fg="white",
                                 insertbackground="white", font=("Segoe UI", 9),
                                 relief="flat", highlightthickness=1,
                                 highlightbackground="#533483", highlightcolor="#e94560")
            val_entry.pack(side="left", padx=(0, 8))
            self.filter_vals.append(val_entry)

            # Bind Enter key
            val_entry.bind("<Return>", lambda e: self.apply_filter())

            # ── Blanks checkbox ──
            blank_var = tk.BooleanVar(value=False)
            self.filter_blanks.append(blank_var)
            tk.Checkbutton(
                row_frame, text="Blanks", variable=blank_var,
                command=self.apply_filter,
                bg="#0f3460", fg="#e94560", selectcolor="#1a1a2e",
                activebackground="#0f3460", activeforeground="#e94560",
                font=("Segoe UI", 9, "bold"), cursor="hand2"
            ).pack(side="left", padx=(0, 6))

        # Apply / Clear buttons in filter bar
        btn_frame_f = tk.Frame(fbar, bg="#0f3460")
        btn_frame_f.grid(row=0, column=2, rowspan=3, padx=12, sticky="ns")

        self._make_btn(btn_frame_f, "Apply Filters", self.apply_filter, "#533483",
                       font=("Segoe UI", 9, "bold"), padx=14, pady=5).pack(pady=3)
        self._make_btn(btn_frame_f, "Clear All",     self.clear_filter, "#333",
                       font=("Segoe UI", 9, "bold"), padx=14, pady=5).pack(pady=3)

        # ── Exclude checkboxes (Fuel / Insurance) ──
        exclude_frame = tk.Frame(fbar, bg="#0f3460")
        exclude_frame.grid(row=0, column=4, rowspan=3, padx=12, sticky="ns")

        tk.Label(exclude_frame, text="Exclude", fg="white", bg="#0f3460",
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")

        self.exclude_fuel_var = tk.BooleanVar(value=False)
        tk.Checkbutton(
            exclude_frame, text="⛽ Fuel", variable=self.exclude_fuel_var,
            command=self.apply_filter,
            bg="#0f3460", fg="#f39c12", selectcolor="#1a1a2e",
            activebackground="#0f3460", activeforeground="#f39c12",
            font=("Segoe UI", 9, "bold"), cursor="hand2"
        ).pack(anchor="w")

        self.exclude_insurance_var = tk.BooleanVar(value=False)
        tk.Checkbutton(
            exclude_frame, text="🛡 Insurance", variable=self.exclude_insurance_var,
            command=self.apply_filter,
            bg="#0f3460", fg="#f39c12", selectcolor="#1a1a2e",
            activebackground="#0f3460", activeforeground="#f39c12",
            font=("Segoe UI", 9, "bold"), cursor="hand2"
        ).pack(anchor="w")

        # Status filter (multi-select checkboxes)
        status_frame = tk.Frame(fbar, bg="#0f3460")
        status_frame.grid(row=0, column=3, rowspan=3, padx=16, sticky="ns")

        tk.Label(status_frame, text="Status", fg="white", bg="#0f3460",
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")

        self.status_filters = {}  # dict of status_label → BooleanVar
        status_options = [
            ("✅ Matched",           "#4ade80"),
            ("📊 Consecutive Match", "#60a5fa"),
            ("🧮 Sum Match",         "#c084fc"),
            ("🔄 Cross Matched",     "#f0ad4e"),
            ("❌ Unmatched",         "#f87171"),
        ]
        for label, color in status_options:
            var = tk.BooleanVar(value=True)  # all checked by default = show all
            self.status_filters[label] = var
            tk.Checkbutton(
                status_frame, text=label, variable=var,
                command=self.apply_filter,
                bg="#0f3460", fg=color, selectcolor="#1a1a2e",
                activebackground="#0f3460", activeforeground=color,
                font=("Segoe UI", 9, "bold"), cursor="hand2"
            ).pack(anchor="w")

        # ── STATS BAR ──
        self.stats_bar = tk.Label(
            self, text="", bg="#0d0d1a", fg="#a8b2d8",
            font=("Segoe UI", 9), anchor="w", padx=12, pady=4
        )
        self.stats_bar.pack(fill="x")

        # ── TABLE ──
        table_frame = tk.Frame(self, bg="#1a1a2e")
        table_frame.pack(fill="both", expand=True, padx=6, pady=4)

        self.tree = ttk.Treeview(table_frame, show="headings", selectmode="extended")
        vsb = ttk.Scrollbar(table_frame, orient="vertical",   command=self.tree.yview)
        hsb = ttk.Scrollbar(table_frame, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        vsb.pack(side="right",  fill="y")
        hsb.pack(side="bottom", fill="x")
        self.tree.pack(fill="both", expand=True)
        self.tree.bind("<Double-1>", lambda e: self.edit_cell())

        # ── Right-click context menu on column headers ──
        self._col_menu = tk.Menu(self, tearoff=0, bg="#1a1a2e", fg="#a8b2d8",
                                  activebackground="#533483", activeforeground="white",
                                  font=("Segoe UI", 9))
        self.tree.bind("<Button-3>", self._on_header_right_click)

        # ── PAGINATION ──
        pbar = tk.Frame(self, bg="#16213e", pady=6)
        pbar.pack(fill="x")

        self._make_btn(pbar, "⏮ First", self.go_first, "#533483", padx=10, pady=4).pack(side="left", padx=4)
        self._make_btn(pbar, "◀ Prev",  self.go_prev,  "#533483", padx=10, pady=4).pack(side="left", padx=4)
        self._make_btn(pbar, "Next ▶",  self.go_next,  "#533483", padx=10, pady=4).pack(side="left", padx=4)
        self._make_btn(pbar, "Last ⏭",  self.go_last,  "#533483", padx=10, pady=4).pack(side="left", padx=4)

        self.lbl_page = tk.Label(pbar, text="Page 0 / 0", fg="#a8b2d8",
                                  bg="#16213e", font=("Segoe UI", 10))
        self.lbl_page.pack(side="left", padx=12)

        tk.Label(pbar, text="Go to page:", fg="#a8b2d8", bg="#16213e",
                 font=("Segoe UI", 9)).pack(side="left", padx=(20, 4))
        self.jump_var = tk.Entry(pbar, width=6, bg="#1a1a2e", fg="white",
                                  insertbackground="white", font=("Segoe UI", 9),
                                  relief="flat", highlightthickness=1,
                                  highlightbackground="#533483")
        self.jump_var.pack(side="left")
        self._make_btn(pbar, "Go", self.go_to_page, "#533483", padx=8, pady=4).pack(side="left", padx=4)

        self.lbl_rows = tk.Label(pbar, text="", fg="#e94560",
                                  bg="#16213e", font=("Segoe UI", 10, "bold"))
        self.lbl_rows.pack(side="right", padx=12)

    def _make_btn(self, parent, text, command, color,
                  font=("Segoe UI", 10, "bold"), padx=12, pady=6):
        btn = tk.Button(
            parent, text=text, command=command,
            bg=color, fg="white",
            activebackground=self._lighten(color),
            activeforeground="white",
            relief="raised", bd=2,
            font=font,
            padx=padx, pady=pady,
            cursor="hand2"
        )
        return btn

    @staticmethod
    def _lighten(hex_color):
        try:
            h = hex_color.lstrip("#")
            r, g, b = int(h[0:2],16), int(h[2:4],16), int(h[4:6],16)
            r = min(255, r + 40)
            g = min(255, g + 40)
            b = min(255, b + 40)
            return f"#{r:02x}{g:02x}{b:02x}"
        except Exception:
            return hex_color

    def _apply_styles(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Treeview",
                         background="#1a1a2e", foreground="#a8b2d8",
                         fieldbackground="#1a1a2e", rowheight=24,
                         font=("Segoe UI", 9))
        style.configure("Treeview.Heading",
                         background="#0f3460", foreground="#e94560",
                         font=("Segoe UI", 9, "bold"), relief="raised")
        style.map("Treeview",
                  background=[("selected", "#533483")],
                  foreground=[("selected", "white")])

    # ── FILE LOADING ──────────────────────────────────────

    def load_file(self):
        path = filedialog.askopenfilename(
            title="Select your data file",
            filetypes=[("Excel files", "*.xlsx *.xls"),
                       ("CSV files", "*.csv"),
                       ("All files", "*.*")]
        )
        if not path:
            return
        self.file_path = path
        self.lbl_file.config(text=f"Loading preview: {os.path.basename(path)} ...")
        self.update_idletasks()
        threading.Thread(target=self._load_preview_thread, args=(path,), daemon=True).start()

    def _load_preview_thread(self, path):
        try:
            ext = os.path.splitext(path)[1].lower()
            if ext in (".xlsx", ".xls"):
                preview_df = pd.read_excel(path, header=None, nrows=20, dtype=str)
            else:
                preview_df = pd.read_csv(path, header=None, nrows=20, dtype=str,
                                         encoding="utf-8-sig")
            self.after(0, self._show_header_popup, path, preview_df)
        except Exception as e:
            self.after(0, lambda: messagebox.showerror("Load Error", str(e)))

    def _show_header_popup(self, path, preview_df):
        popup = tk.Toplevel(self)
        popup.title("Select Header Row")
        popup.configure(bg="#1a1a2e")
        popup.geometry("900x580")
        popup.grab_set()

        tk.Label(popup,
                 text="📋  First 20 rows of your file are shown below.\n"
                      "Click the row that contains column headers, then press  🚀 Proceed.",
                 font=("Segoe UI", 10), fg="#a8b2d8", bg="#1a1a2e",
                 justify="left").pack(padx=16, pady=(12, 6), anchor="w")

        frame = tk.Frame(popup, bg="#1a1a2e")
        frame.pack(fill="both", expand=True, padx=12, pady=4)

        cols = [f"Col {i+1}" for i in range(len(preview_df.columns))]
        tree = ttk.Treeview(frame, columns=["#"] + cols, show="headings",
                            height=16, selectmode="browse")
        vsb = ttk.Scrollbar(frame, orient="vertical",   command=tree.yview)
        hsb = ttk.Scrollbar(frame, orient="horizontal", command=tree.xview)
        tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        vsb.pack(side="right", fill="y")
        hsb.pack(side="bottom", fill="x")
        tree.pack(fill="both", expand=True)

        tree.heading("#", text="Row #")
        tree.column("#", width=55, anchor="center")
        for c in cols:
            tree.heading(c, text=c)
            tree.column(c, width=110, minwidth=60)

        row_iids = []
        for i, row in preview_df.iterrows():
            vals = [str(v) if pd.notna(v) else "" for v in row]
            iid = tree.insert("", "end", values=[i] + vals, tags=("normal",))
            row_iids.append(iid)

        tree.tag_configure("normal",   background="#1a1a2e", foreground="#a8b2d8")
        tree.tag_configure("selected", background="#533483", foreground="white")

        selected_row = tk.IntVar(value=-1)

        lbl_sel = tk.Label(popup, text="⬆  Click a row above to select it as the header",
                           fg="#a8b2d8", bg="#1a1a2e",
                           font=("Segoe UI", 10, "bold"))
        lbl_sel.pack(pady=(6, 2))

        def on_click(event):
            item = tree.focus()
            if not item:
                return
            for iid in row_iids:
                tree.item(iid, tags=("normal",))
            tree.item(item, tags=("selected",))
            row_num = int(tree.item(item, "values")[0])
            selected_row.set(row_num)
            lbl_sel.config(
                text=f"✅  Row {row_num} selected as header — press  🚀 Proceed  to load",
                fg="#e94560"
            )
            proceed_btn.config(
                text=f"🚀  Proceed with Row {row_num} as Header",
                state="normal"
            )

        tree.bind("<<TreeviewSelect>>", on_click)

        btn_frame = tk.Frame(popup, bg="#1a1a2e")
        btn_frame.pack(pady=10)

        def proceed_with_selected():
            hr = selected_row.get()
            if hr < 0:
                messagebox.showwarning("Select Row",
                                       "Please click a row first to select it as the header.",
                                       parent=popup)
                return
            popup.destroy()
            self.lbl_file.config(text=f"Loading full file (header = row {hr})…")
            self.update_idletasks()
            threading.Thread(target=self._load_thread, args=(path, hr), daemon=True).start()

        proceed_btn = tk.Button(
            btn_frame,
            text="🚀  Proceed with Selected Row as Header",
            command=proceed_with_selected,
            bg="#0f6e56", fg="white",
            activebackground=self._lighten("#0f6e56"),
            activeforeground="white",
            relief="raised", bd=2,
            font=("Segoe UI", 11, "bold"),
            padx=18, pady=8,
            cursor="hand2",
            state="disabled"
        )
        proceed_btn.pack(side="left", padx=8)

        def use_first():
            popup.destroy()
            self.lbl_file.config(text="Loading full file (header = row 0)…")
            self.update_idletasks()
            threading.Thread(target=self._load_thread, args=(path, 0), daemon=True).start()

        self._make_btn(btn_frame, "⚡ Use Row 0 (default)",
                       use_first, "#533483").pack(side="left", padx=8)
        self._make_btn(btn_frame, "❌ Cancel",
                       popup.destroy, "#555").pack(side="left", padx=8)

    def _load_thread(self, path, header_row=0):
        try:
            ext = os.path.splitext(path)[1].lower()
            if ext in (".xlsx", ".xls"):
                df = pd.read_excel(path, header=header_row, dtype=str)
            else:
                df = pd.read_csv(path, header=header_row, dtype=str,
                                 encoding="utf-8-sig")

            # Store raw df temporarily — column mapping popup will finalise it
            self._raw_df = df
            self.after(0, self._show_column_mapping, path)
        except Exception as e:
            self.after(0, lambda: messagebox.showerror("Load Error", str(e)))

    # ── COLUMN MAPPING POPUP ─────────────────────────────

    def _show_column_mapping(self, path):
        """Show a form to map config variables to actual file columns."""
        global COL_DATE, COL_DEBIT, COL_CREDIT, COL_OP_DATA, COL_EXP_TYPE, COL_NAME

        df = self._raw_df
        file_cols = list(df.columns)

        popup = tk.Toplevel(self)
        popup.title("🗂  Map Columns")
        popup.configure(bg="#1a1a2e")
        popup.geometry("600x540")
        popup.grab_set()

        tk.Label(popup,
                 text="🗂  Column Mapping",
                 font=("Segoe UI", 14, "bold"), fg="#e94560", bg="#1a1a2e"
                 ).pack(padx=20, pady=(16, 4), anchor="w")

        tk.Label(popup,
                 text="Map each required field to the correct column in your file.\n"
                      "The dropdowns are pre-filled with the best guess.",
                 font=("Segoe UI", 9), fg="#a8b2d8", bg="#1a1a2e",
                 justify="left"
                 ).pack(padx=20, pady=(0, 12), anchor="w")

        # Config fields with their current defaults and hints for matching
        mapping_fields = [
            ("Date Column",         COL_DATE,     ["date", "post date", "posting date", "txn date", "transaction date"]),
            ("Debit Column",        COL_DEBIT,    ["debit", "dr", "debit amount"]),
            ("Credit Column",       COL_CREDIT,   ["credit", "cr", "credit amount"]),
            ("All OP Data Column",  COL_OP_DATA,  ["all op data", "op data", "party"]),
            ("Name Column",         COL_NAME,     ["name", "driver name", "employee", "driver", "employee name"]),
            ("Expense Type Column", COL_EXP_TYPE, ["expense type", "type", "category", "expense"]),
        ]

        combos = {}
        form_frame = tk.Frame(popup, bg="#1a1a2e")
        form_frame.pack(fill="x", padx=20, pady=4)

        # Helper: find the best matching column
        def best_match(hints, current_default):
            # First check if the exact default exists in the file
            if current_default in file_cols:
                return current_default
            # Then try case-insensitive match on hints
            lower_cols = {c.lower().strip(): c for c in file_cols}
            for hint in hints:
                if hint.lower() in lower_cols:
                    return lower_cols[hint.lower()]
            # Partial match
            for hint in hints:
                for lc, orig in lower_cols.items():
                    if hint.lower() in lc or lc in hint.lower():
                        return orig
            # Fallback: return first column
            return file_cols[0] if file_cols else ""

        for i, (label, default, hints) in enumerate(mapping_fields):
            row_frame = tk.Frame(form_frame, bg="#1a1a2e")
            row_frame.pack(fill="x", pady=6)

            tk.Label(row_frame, text=label, fg="#a8b2d8", bg="#1a1a2e",
                     font=("Segoe UI", 10, "bold"), width=22, anchor="w"
                     ).pack(side="left", padx=(0, 8))

            # "None" option for optional columns
            options = ["(None — skip)"] + file_cols
            cb = ttk.Combobox(row_frame, values=options, state="readonly",
                              font=("Segoe UI", 10), width=28)
            cb.pack(side="left")

            matched = best_match(hints, default)
            cb.set(matched if matched else "(None — skip)")
            combos[label] = cb

            # Show a small preview of the matched column (first value)
            preview = ""
            if matched and matched in df.columns:
                first_vals = df[matched].dropna().head(3).tolist()
                preview = ", ".join(str(v) for v in first_vals[:3])
                if len(preview) > 40:
                    preview = preview[:40] + "…"
            prev_lbl = tk.Label(row_frame, text=f"  e.g. {preview}" if preview else "",
                                fg="#666", bg="#1a1a2e", font=("Segoe UI", 8))
            prev_lbl.pack(side="left", padx=6)

            # Update preview on selection change
            def on_select(event, combo=cb, lbl=prev_lbl):
                sel = combo.get()
                if sel == "(None — skip)" or sel not in df.columns:
                    lbl.config(text="")
                    return
                vals = df[sel].dropna().head(3).tolist()
                txt = ", ".join(str(v) for v in vals[:3])
                if len(txt) > 40:
                    txt = txt[:40] + "…"
                lbl.config(text=f"  e.g. {txt}")
            cb.bind("<<ComboboxSelected>>", on_select)

        # Buttons
        btn_frame = tk.Frame(popup, bg="#1a1a2e")
        btn_frame.pack(pady=16)

        def confirm_mapping():
            nonlocal popup
            global COL_DATE, COL_DEBIT, COL_CREDIT, COL_OP_DATA, COL_EXP_TYPE

            selections = {}
            for label, cb in combos.items():
                val = cb.get()
                selections[label] = val if val != "(None — skip)" else None

            COL_DATE     = selections.get("Date Column")         or COL_DATE
            COL_DEBIT    = selections.get("Debit Column")        or COL_DEBIT
            COL_CREDIT   = selections.get("Credit Column")       or COL_CREDIT
            COL_OP_DATA  = selections.get("All OP Data Column")  or COL_OP_DATA
            COL_NAME     = selections.get("Name Column")         or COL_NAME
            COL_EXP_TYPE = selections.get("Expense Type Column") or COL_EXP_TYPE

            # make an explicit copy so pandas doesn't silently skip assignments
            df = self._raw_df.copy()

            # Convert numeric columns
            for col in [COL_DEBIT, COL_CREDIT]:
                if col in df.columns:
                    df[col] = pd.to_numeric(df[col], errors="coerce")

            # ── Clean all text columns: strip spaces + lowercase ──
            # No dtype guard — works with object, StringDtype, or any str-convertible column
            numeric_cols = {COL_DEBIT, COL_CREDIT}
            cells_cleaned = 0
            for col in list(df.columns):
                if col in numeric_cols:
                    continue
                try:
                    nan_mask     = df[col].isna()                      # remember where NaNs were
                    original_str = df[col].fillna("").astype(str)      # safe string conversion
                    cleaned_str  = original_str.str.strip().str.lower()
                    cells_cleaned += int((original_str != cleaned_str).sum())
                    # write back, restoring original NaNs
                    df[col] = cleaned_str.where(~nan_mask, other=np.nan)
                except Exception:
                    pass  # leave column untouched if something unexpected happens

            self.df_original = df
            self.df_display  = df.copy()
            popup.destroy()
            self._on_load_complete(path, cells_cleaned)

        self._make_btn(btn_frame, "✅  Confirm Mapping", confirm_mapping, "#0f6e56",
                       font=("Segoe UI", 11, "bold"), padx=18, pady=8
                       ).pack(side="left", padx=8)
        self._make_btn(btn_frame, "❌  Cancel", popup.destroy, "#555"
                       ).pack(side="left", padx=8)

    def _on_load_complete(self, path, cells_cleaned=0):
        df = self.df_original
        clean_note = f"  |  🧹 {cells_cleaned:,} cells cleaned (stripped + lowercased)" if cells_cleaned else ""
        self.lbl_file.config(
            text=f"✅ {os.path.basename(path)}  ({len(df):,} rows){clean_note}"
        )
        self._setup_columns()
        self._refresh_filter_cols()
        self._paginate_and_show()

    # ── COLUMN SETUP ─────────────────────────────────────

    def _setup_columns(self):
        cols = list(self.df_display.columns)
        if "_status" in cols:
            cols = ["_status", "_match_id"] + [c for c in cols if c not in ("_status","_match_id","_matched","_match_note")]
        # Filter out hidden columns
        cols = [c for c in cols if c not in self.hidden_columns]
        self.tree["columns"] = cols
        for col in cols:
            width = 120 if col not in ("_status","_match_id") else 100
            self.tree.heading(col, text=col, command=lambda c=col: self._sort_col(c))
            self.tree.column(col, width=width, minwidth=60, stretch=False)

    # ── PAGINATION ───────────────────────────────────────

    def _paginate_and_show(self):
        if self.df_display is None: return
        n = len(self.df_display)
        self.total_pages = max(1, (n + PAGE_SIZE - 1) // PAGE_SIZE)
        self.current_page = min(self.current_page, self.total_pages - 1)
        self._render_page()
        self._update_stats()

    def _render_page(self):
        self.tree.delete(*self.tree.get_children())
        if self.df_display is None or len(self.df_display) == 0:
            return

        start = self.current_page * PAGE_SIZE
        end   = min(start + PAGE_SIZE, len(self.df_display))
        chunk = self.df_display.iloc[start:end]

        cols = list(self.tree["columns"])
        for _, row in chunk.iterrows():
            vals = [str(row[c]) if c in row.index and pd.notna(row[c]) else "" for c in cols]
            if "_status" in row.index:
                st = row["_status"]
                if st == "📊 Consecutive Match":
                    tag = "consec_matched"
                elif st == "🧮 Sum Match":
                    tag = "sum_matched"
                elif st == "✅ Matched":
                    tag = "matched"
                elif st == "🔄 Cross Matched":
                    tag = "cross_matched"
                else:
                    tag = ""
            else:
                tag = ""
            self.tree.insert("", "end", values=vals, tags=(tag,))

        self.tree.tag_configure("matched",         background="#1a3d2b", foreground="#4ade80")
        self.tree.tag_configure("consec_matched",  background="#1a2d4d", foreground="#60a5fa")
        self.tree.tag_configure("sum_matched",     background="#2d1a4d", foreground="#c084fc")
        self.tree.tag_configure("cross_matched",   background="#3d2d1a", foreground="#f0ad4e")

        self.lbl_page.config(text=f"Page {self.current_page+1} / {self.total_pages}")
        self.lbl_rows.config(text=f"Total rows: {len(self.df_display):,}")

    def _update_stats(self):
        df = self.df_display
        if df is None: return
        total = len(df)
        if "_status" in df.columns:
            exact_matched   = len(df[df["_status"] == "✅ Matched"])
            consec_matched  = len(df[df["_status"] == "📊 Consecutive Match"])
            sum_matched     = len(df[df["_status"] == "🧮 Sum Match"])
            matched         = exact_matched + consec_matched + sum_matched
            cross_matched   = len(df[df["_status"] == "🔄 Cross Matched"])
            unmatched       = len(df[df["_status"] == "❌ Unmatched"])
        else:
            matched = cross_matched = unmatched = consec_matched = sum_matched = "N/A"
        debit_sum  = pd.to_numeric(df[COL_DEBIT],  errors="coerce").sum() if COL_DEBIT  in df.columns else 0
        credit_sum = pd.to_numeric(df[COL_CREDIT], errors="coerce").sum() if COL_CREDIT in df.columns else 0
        self.stats_bar.config(
            text=f"  Rows: {total:,}   |   Matched: {matched}   |   Consecutive: {consec_matched}   "
                 f"|   Sum: {sum_matched}   |   Cross: {cross_matched}   |   Unmatched: {unmatched}   "
                 f"|   Total Debit: ₹{debit_sum:,.2f}   |   Total Credit: ₹{credit_sum:,.2f}"
        )

    # ── PAGINATION CONTROLS ───────────────────────────────

    def go_first(self): self.current_page = 0;                          self._render_page()
    def go_last(self):  self.current_page = self.total_pages - 1;       self._render_page()
    def go_prev(self):
        if self.current_page > 0:
            self.current_page -= 1
            self._render_page()
    def go_next(self):
        if self.current_page < self.total_pages - 1:
            self.current_page += 1
            self._render_page()
    def go_to_page(self):
        try:
            p = int(self.jump_var.get()) - 1
            if 0 <= p < self.total_pages:
                self.current_page = p
                self._render_page()
        except ValueError:
            pass

    # ── SORT ─────────────────────────────────────────────

    def _sort_col(self, col):
        if self.df_display is None: return
        asc = not getattr(self, f"_sort_asc_{col}", True)
        setattr(self, f"_sort_asc_{col}", asc)
        self.df_display = self.df_display.sort_values(col, ascending=asc, na_position="last")
        self.df_display.reset_index(drop=True, inplace=True)
        self.current_page = 0
        self._render_page()

    # ── FILTER (TRIPLE) ───────────────────────────────────

    def _refresh_filter_cols(self):
        if self.df_original is not None:
            cols = list(self.df_original.columns)
            for cb in self.filter_cols:
                cb["values"] = cols
                if cols:
                    cb.set(cols[0])

    def apply_filter(self):
        if self.df_original is None: return
        df = self.df_original.copy()

        for col_cb, val_entry, blank_var in zip(
                self.filter_cols, self.filter_vals, self.filter_blanks):
            col = col_cb.get()
            if not col or col not in df.columns:
                continue

            if blank_var.get():
                # Show only rows where this column is blank / NaN
                df = df[
                    df[col].isna() |
                    (df[col].astype(str).str.strip() == "") |
                    (df[col].astype(str).str.strip() == "nan")
                ]
            else:
                val = val_entry.get().strip()
                if val:
                    # Support comma-separated OR filtering (e.g. "advance,repair")
                    if "," in val:
                        parts = [p.strip() for p in val.split(",") if p.strip()]
                        if parts:
                            combined_mask = df[col].astype(str).str.contains(
                                parts[0], case=False, na=False)
                            for part in parts[1:]:
                                combined_mask = combined_mask | df[col].astype(str).str.contains(
                                    part, case=False, na=False)
                            df = df[combined_mask]
                    else:
                        df = df[df[col].astype(str).str.contains(val, case=False, na=False)]

        # ── Exclude Fuel / Insurance ──
        if COL_EXP_TYPE in df.columns:
            exclude_types = []
            if self.exclude_fuel_var.get():
                exclude_types.append("fuel")
            if self.exclude_insurance_var.get():
                exclude_types.append("insurance")
            if exclude_types:
                df = df[~df[COL_EXP_TYPE].astype(str).str.strip().str.lower().isin(exclude_types)]

        # Status filter (multi-select checkboxes)
        if "_status" in df.columns and hasattr(self, 'status_filters'):
            # Check if any filter is unchecked (not all True)
            selected_statuses = [lbl for lbl, var in self.status_filters.items() if var.get()]
            all_checked = len(selected_statuses) == len(self.status_filters)
            if not all_checked and selected_statuses:
                df = df[df["_status"].isin(selected_statuses)]
            elif not all_checked and not selected_statuses:
                # Nothing selected → show nothing
                df = df.iloc[0:0]

        self.df_display = df
        self.current_page = 0
        self._setup_columns()
        self._paginate_and_show()

    def clear_filter(self):
        for val_entry in self.filter_vals:
            val_entry.delete(0, "end")
        for blank_var in self.filter_blanks:
            blank_var.set(False)
        self.exclude_fuel_var.set(False)
        self.exclude_insurance_var.set(False)
        if hasattr(self, 'status_filters'):
            for var in self.status_filters.values():
                var.set(True)
        if self.df_original is not None:
            self.df_display = self.df_original.copy()
            self.current_page = 0
            self._setup_columns()
            self._paginate_and_show()

    # ── RECONCILIATION ────────────────────────────────────

    def run_recon(self):
        if self.df_original is None:
            messagebox.showwarning("No Data", "Please load a file first.")
            return
        self.lbl_file.config(text="⏳ Running reconciliation...")
        self.update_idletasks()
        threading.Thread(target=self._recon_thread, daemon=True).start()

    def _recon_progress(self, msg):
        """Thread-safe progress update for reconciliation."""
        self.after(0, lambda: self.lbl_file.config(text=f"⏳ {msg}"))

    def _recon_thread(self):
        try:
            result = run_reconciliation(self.df_original,
                                        progress_cb=self._recon_progress)
            self.df_original = result
            self.df_display  = result.copy()
            self.after(0, self._on_recon_complete)
        except Exception as e:
            import traceback
            err_msg = f"{e}\n\n{traceback.format_exc()}"
            self.after(0, lambda: self._on_recon_error(err_msg))

    def _on_recon_error(self, err_msg):
        self.lbl_file.config(text="❌ Reconciliation failed!")
        messagebox.showerror("Reconciliation Error", err_msg)

    def _on_recon_complete(self):
        self.lbl_file.config(text="✅ Reconciliation complete!")
        self.current_page = 0
        self._setup_columns()
        self._refresh_filter_cols()
        self._paginate_and_show()
        self._auto_save()
        messagebox.showinfo("Done", "Reconciliation complete!\nMatched/Unmatched status is now visible.")

    # ── SHOW MATCH ────────────────────────────────────────

    def show_match(self):
        """Show all rows that share the same match ID as the selected row."""
        selected = self.tree.selection()
        if not selected:
            messagebox.showwarning("Select Row", "Please select a row first.")
            return

        if self.df_display is None or "_match_id" not in self.df_display.columns:
            messagebox.showwarning("No Match Data", "Please run reconciliation first.")
            return

        item = selected[0]
        cols = list(self.tree["columns"])
        values = self.tree.item(item, "values")

        match_id_col_idx = None
        for i, c in enumerate(cols):
            if c == "_match_id":
                match_id_col_idx = i
                break

        if match_id_col_idx is None or match_id_col_idx >= len(values):
            messagebox.showwarning("No Match Data",
                                   "Match ID column not found. Run reconciliation first.")
            return

        mid = values[match_id_col_idx].strip()
        if not mid:
            messagebox.showinfo("Unmatched",
                                "This row is not matched with any other row (❌ Unmatched).")
            return

        matched_df = self.df_original[self.df_original["_match_id"] == mid].copy()
        if matched_df.empty:
            messagebox.showinfo("Not Found", f"No rows found with Match ID: {mid}")
            return

        match_note = ""
        if "_match_note" in matched_df.columns:
            notes = matched_df["_match_note"].dropna().unique()
            if len(notes) > 0:
                match_note = str(notes[0])

        # ── Build the popup ──
        popup = tk.Toplevel(self)
        popup.title(f"🔗 Match Group — {mid}")
        popup.configure(bg="#1a1a2e")
        popup.geometry("1100x600")
        popup.grab_set()

        tk.Label(popup,
                 text=f"🔗  Match ID: {mid}",
                 font=("Segoe UI", 13, "bold"), fg="#e94560", bg="#1a1a2e"
                 ).pack(padx=16, pady=(12, 2), anchor="w")

        if match_note:
            tk.Label(popup,
                     text=f"📋  {match_note}",
                     font=("Segoe UI", 10), fg="#4ade80", bg="#1a1a2e"
                     ).pack(padx=16, pady=(0, 2), anchor="w")

        count_lbl = tk.Label(popup,
                 text=f"{len(matched_df)} entries in this match group",
                 font=("Segoe UI", 9), fg="#a8b2d8", bg="#1a1a2e")
        count_lbl.pack(padx=16, pady=(0, 4), anchor="w")

        show_cols = [c for c in matched_df.columns if c not in ("_matched", "_match_note")]

        # ── FILTER BAR (triple) ──
        fbar = tk.Frame(popup, bg="#0f3460", pady=6)
        fbar.pack(fill="x", padx=0)

        tk.Label(fbar, text="  Filters:", fg="white", bg="#0f3460",
                 font=("Segoe UI", 9, "bold")).grid(row=0, column=0, rowspan=3, padx=(8, 4), sticky="ns")

        popup_filter_cols = []
        popup_filter_vals = []
        filter_labels = ["Filter 1:", "Filter 2:", "Filter 3:"]

        for fi in range(3):
            row_frame = tk.Frame(fbar, bg="#0f3460")
            row_frame.grid(row=fi, column=1, sticky="w", pady=1, padx=4)

            tk.Label(row_frame, text=filter_labels[fi], fg="#a8b2d8", bg="#0f3460",
                     font=("Segoe UI", 8), width=7, anchor="e").pack(side="left")

            col_cb = ttk.Combobox(row_frame, width=14, state="readonly",
                                  font=("Segoe UI", 8), values=show_cols)
            col_cb.pack(side="left", padx=(4, 4))

            main_col = self.filter_cols[fi].get() if fi < len(self.filter_cols) else ""
            main_val = self.filter_vals[fi].get().strip() if fi < len(self.filter_vals) else ""
            if main_col and main_col in show_cols:
                col_cb.set(main_col)
            elif show_cols:
                col_cb.set(show_cols[0])

            popup_filter_cols.append(col_cb)

            val_entry = tk.Entry(row_frame, width=16, bg="#1a1a2e", fg="white",
                                 insertbackground="white", font=("Segoe UI", 8),
                                 relief="flat", highlightthickness=1,
                                 highlightbackground="#533483", highlightcolor="#e94560")
            val_entry.pack(side="left", padx=(0, 6))
            if main_val:
                val_entry.insert(0, main_val)
            popup_filter_vals.append(val_entry)

        btn_frame_f = tk.Frame(fbar, bg="#0f3460")
        btn_frame_f.grid(row=0, column=2, rowspan=3, padx=8, sticky="ns")

        # ── Table ──
        tbl_frame = tk.Frame(popup, bg="#1a1a2e")
        tbl_frame.pack(fill="both", expand=True, padx=10, pady=4)

        match_tree = ttk.Treeview(tbl_frame, columns=show_cols, show="headings", height=18)
        vsb = ttk.Scrollbar(tbl_frame, orient="vertical",   command=match_tree.yview)
        hsb = ttk.Scrollbar(tbl_frame, orient="horizontal", command=match_tree.xview)
        match_tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        vsb.pack(side="right",  fill="y")
        hsb.pack(side="bottom", fill="x")
        match_tree.pack(fill="both", expand=True)

        for c in show_cols:
            match_tree.heading(c, text=c)
            w = 100 if c not in ("_status", "_match_id") else 90
            match_tree.column(c, width=w, minwidth=50, stretch=False)

        match_tree.tag_configure("debit",  background="#2d1a1a", foreground="#f87171")
        match_tree.tag_configure("credit", background="#1a3d2b", foreground="#4ade80")

        # ── Summary ──
        summary_frame = tk.Frame(popup, bg="#16213e")
        summary_frame.pack(fill="x", padx=10, pady=6)
        summary_lbl = tk.Label(summary_frame, text="",
                 font=("Segoe UI", 10, "bold"), fg="#a8b2d8", bg="#16213e")
        summary_lbl.pack(side="left", padx=10, pady=6)

        self._make_btn(summary_frame, "❌ Close", popup.destroy, "#555",
                       padx=12, pady=4).pack(side="right", padx=10, pady=4)

        # ── Render / filter logic ──
        def render_match_table(df_to_show):
            match_tree.delete(*match_tree.get_children())
            for _, row in df_to_show.iterrows():
                vals = [str(row[c]) if c in row.index and pd.notna(row[c]) else "" for c in show_cols]
                d_val = row.get(COL_DEBIT, None)
                try:
                    tag = "debit" if (pd.notna(d_val) and float(d_val) != 0) else "credit"
                except (ValueError, TypeError):
                    tag = "credit"
                match_tree.insert("", "end", values=vals, tags=(tag,))

            debit_total  = pd.to_numeric(df_to_show[COL_DEBIT],  errors="coerce").sum() if COL_DEBIT  in df_to_show.columns else 0
            credit_total = pd.to_numeric(df_to_show[COL_CREDIT], errors="coerce").sum() if COL_CREDIT in df_to_show.columns else 0
            summary_lbl.config(
                text=f"Debit Total: ₹{debit_total:,.2f}   |   Credit Total: ₹{credit_total:,.2f}   |   "
                     f"Net: ₹{debit_total - credit_total:,.2f}   |   Entries: {len(df_to_show)}"
            )
            count_lbl.config(text=f"{len(df_to_show)} entries shown")

        def apply_popup_filter():
            df_filtered = matched_df.copy()
            for col_cb, val_entry in zip(popup_filter_cols, popup_filter_vals):
                col = col_cb.get()
                val = val_entry.get().strip()
                if col and val and col in df_filtered.columns:
                    df_filtered = df_filtered[
                        df_filtered[col].astype(str).str.contains(val, case=False, na=False)
                    ]
            render_match_table(df_filtered)

        def clear_popup_filter():
            for ve in popup_filter_vals:
                ve.delete(0, "end")
            render_match_table(matched_df)

        self._make_btn(btn_frame_f, "Apply",  apply_popup_filter, "#533483",
                       font=("Segoe UI", 8, "bold"), padx=10, pady=4).pack(pady=2)
        self._make_btn(btn_frame_f, "Clear",  clear_popup_filter, "#333",
                       font=("Segoe UI", 8, "bold"), padx=10, pady=4).pack(pady=2)

        for ve in popup_filter_vals:
            ve.bind("<Return>", lambda e: apply_popup_filter())

        # Initial render
        render_match_table(matched_df)

    # ── ADD COLUMN ────────────────────────────────────────

    def add_column(self):
        if self.df_original is None:
            messagebox.showwarning("No Data", "Please load a file first.")
            return

        popup = tk.Toplevel(self)
        popup.title("➕  Add Computed Column")
        popup.configure(bg="#1a1a2e")
        popup.geometry("750x780")
        popup.grab_set()

        tk.Label(popup,
                 text="➕  Add New Computed Column",
                 font=("Segoe UI", 13, "bold"), fg="#e94560", bg="#1a1a2e"
                 ).pack(padx=20, pady=(14, 2), anchor="w")

        tk.Label(popup,
                 text="Write Python code below. Use  df  to reference your data.\n"
                      "For multi-line code, assign the final column values to  result.",
                 font=("Segoe UI", 9), fg="#a8b2d8", bg="#1a1a2e",
                 justify="left"
                 ).pack(padx=20, pady=(0, 10), anchor="w")

        # Column name
        name_frame = tk.Frame(popup, bg="#1a1a2e")
        name_frame.pack(fill="x", padx=20, pady=4)
        tk.Label(name_frame, text="Column Name:", fg="#a8b2d8", bg="#1a1a2e",
                 font=("Segoe UI", 10, "bold"), width=14, anchor="w"
                 ).pack(side="left")
        name_entry = tk.Entry(name_frame, width=30, bg="#0f3460", fg="white",
                              insertbackground="white", font=("Segoe UI", 10))
        name_entry.pack(side="left", padx=8)

        # Code editor
        expr_frame = tk.Frame(popup, bg="#1a1a2e")
        expr_frame.pack(fill="x", padx=20, pady=(10, 2))
        tk.Label(expr_frame, text="Python Code:", fg="#a8b2d8", bg="#1a1a2e",
                 font=("Segoe UI", 10, "bold"), anchor="w"
                 ).pack(anchor="w")

        expr_text = tk.Text(popup, height=6, bg="#0f3460", fg="white",
                            insertbackground="white", font=("Consolas", 10),
                            relief="flat", highlightthickness=1,
                            highlightbackground="#533483", highlightcolor="#e94560",
                            wrap="word", undo=True)
        expr_text.pack(fill="x", padx=20, pady=(2, 6))

        def handle_tab(event):
            expr_text.insert("insert", "    ")
            return "break"
        expr_text.bind("<Tab>", handle_tab)

        examples_text = (
            "Examples (single-line — no 'result' needed):\n"
            "  pd.to_datetime(df['Memo'].str[:10], format='%m/%d/%Y', errors='coerce')\n"
            "  df['Debit'].fillna(0).astype(float) * 2\n\n"
            "Examples (multi-line — assign to 'result'):\n"
            "  keywords = ['Advance', 'Fuel', 'Void', 'Repair']\n"
            "  def fill(row):\n"
            "      memo = str(row['Memo']).lower()\n"
            "      for kw in keywords:\n"
            "          if kw.lower() in memo: return kw\n"
            "      return row['Expense Type']\n"
            "  result = df.apply(fill, axis=1)"
        )
        tk.Label(popup, text=examples_text, fg="#666", bg="#1a1a2e",
                 font=("Consolas", 8), justify="left", anchor="w"
                 ).pack(padx=20, pady=(0, 6), anchor="w")

        # ── Helper functions (must be defined before buttons reference them) ──

        def _build_namespace(df):
            return {"df": df, "pd": pd, "np": np, "result": None,
                    "str": str, "int": int, "float": float,
                    "len": len, "round": round, "abs": abs,
                    "min": min, "max": max, "list": list, "dict": dict,
                    "range": range, "enumerate": enumerate, "zip": zip,
                    "isinstance": isinstance, "type": type, "set": set,
                    "sorted": sorted, "map": map, "filter": filter,
                    "True": True, "False": False, "None": None,
                    "print": print, "tuple": tuple, "bool": bool,
                    "any": any, "all": all, "sum": sum,
                    "__builtins__": {}}

        def _run_code(code, df):
            """Run code — try eval first (single expression), fall back to exec (multi-line)."""
            ns = _build_namespace(df)
            try:
                result = eval(code, ns, ns)
                return result
            except SyntaxError:
                pass
            ns2 = _build_namespace(df)
            exec(code, ns2, ns2)
            if ns2.get("result") is not None:
                return ns2["result"]
            raise ValueError("Multi-line code must assign the column values to a variable called 'result'.\n"
                             "Example:  result = df.apply(my_func, axis=1)")

        def do_preview():
            preview_tree.delete(*preview_tree.get_children())
            col_name = name_entry.get().strip()
            code = expr_text.get("1.0", "end").strip()

            if not col_name:
                status_lbl.config(text="⚠  Please enter a column name.", fg="#f87171")
                return
            if not code:
                status_lbl.config(text="⚠  Please enter code.", fg="#f87171")
                return

            try:
                df = self.df_original.copy()
                result = _run_code(code, df)

                if not hasattr(result, '__len__') or isinstance(result, str):
                    result = pd.Series([result] * len(df))

                for i in range(min(5, len(df))):
                    try:
                        val = result.iloc[i] if hasattr(result, 'iloc') else result[i]
                        preview_tree.insert("", "end", values=[i, str(val)])
                    except Exception:
                        preview_tree.insert("", "end", values=[i, "(error)"])

                status_lbl.config(
                    text=f"✅  Preview OK — {len(df):,} values will be computed.",
                    fg="#4ade80"
                )
            except Exception as e:
                status_lbl.config(text=f"❌  Error: {e}", fg="#f87171")

        def do_apply():
            col_name = name_entry.get().strip()
            code = expr_text.get("1.0", "end").strip()

            if not col_name:
                messagebox.showwarning("Missing Name", "Please enter a column name.", parent=popup)
                return
            if not code:
                messagebox.showwarning("Missing Code", "Please enter code.", parent=popup)
                return

            try:
                df = self.df_original
                result = _run_code(code, df)

                if not hasattr(result, '__len__') or isinstance(result, str):
                    result = pd.Series([result] * len(df), index=df.index)

                self.df_original[col_name] = result
                self.df_display = self.df_original.copy()
                self._setup_columns()
                self._refresh_filter_cols()
                self._paginate_and_show()
                self._auto_save()
                popup.destroy()
                messagebox.showinfo("Done", f"Column '{col_name}' added successfully!")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to compute column:\n{e}", parent=popup)

        # ── Bottom section: buttons + status (packed with side=bottom so they
        #    are always visible, even if the window is too small) ──
        btn_frame = tk.Frame(popup, bg="#1a1a2e")
        btn_frame.pack(side="bottom", fill="x", pady=(6, 12), padx=20)

        self._make_btn(btn_frame, "👁  Preview", do_preview, "#185fa5",
                       padx=14, pady=6).pack(side="left", padx=6)
        self._make_btn(btn_frame, "✅  Apply", do_apply, "#0f6e56",
                       padx=14, pady=6).pack(side="left", padx=6)
        self._make_btn(btn_frame, "❌  Cancel", popup.destroy, "#555",
                       padx=14, pady=6).pack(side="left", padx=6)

        status_lbl = tk.Label(popup, text="", fg="#a8b2d8", bg="#1a1a2e",
                               font=("Segoe UI", 9, "bold"))
        status_lbl.pack(side="bottom", padx=20, anchor="w")

        # ── Preview area (fills remaining space above buttons) ──
        preview_frame = tk.Frame(popup, bg="#1a1a2e")
        preview_frame.pack(fill="both", expand=True, padx=20, pady=4)

        tk.Label(preview_frame, text="Preview (first 5 rows):",
                 fg="#a8b2d8", bg="#1a1a2e",
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")

        preview_tree = ttk.Treeview(preview_frame, columns=["Row", "Value"],
                                     show="headings", height=5)
        preview_tree.heading("Row", text="Row #")
        preview_tree.heading("Value", text="Computed Value")
        preview_tree.column("Row", width=60, anchor="center")
        preview_tree.column("Value", width=550)
        preview_tree.pack(fill="both", expand=True, pady=4)

    # ── HIDE / SHOW COLUMNS ──────────────────────────────

    def _on_header_right_click(self, event):
        """Right-click on a column header → show hide/delete menu."""
        region = self.tree.identify_region(event.x, event.y)
        if region != "heading":
            return
        col_id = self.tree.identify_column(event.x)
        if not col_id:
            return
        try:
            col_index = int(col_id.replace("#", "")) - 1
            visible_cols = list(self.tree["columns"])
            if col_index < 0 or col_index >= len(visible_cols):
                return
            col_name = visible_cols[col_index]
        except (ValueError, IndexError):
            return

        self._col_menu.delete(0, "end")
        self._col_menu.add_command(
            label=f"👁  Hide '{col_name}'",
            command=lambda c=col_name: self._quick_hide_column(c)
        )
        self._col_menu.add_command(
            label=f"🗑  Delete '{col_name}' permanently",
            command=lambda c=col_name: self._quick_delete_column(c)
        )
        self._col_menu.add_separator()
        if self.hidden_columns:
            unhide_menu = tk.Menu(self._col_menu, tearoff=0, bg="#1a1a2e", fg="#a8b2d8",
                                   activebackground="#533483", activeforeground="white",
                                   font=("Segoe UI", 9))
            for hc in sorted(self.hidden_columns):
                unhide_menu.add_command(
                    label=hc,
                    command=lambda c=hc: self._quick_unhide_column(c)
                )
            self._col_menu.add_cascade(label="👁  Unhide column…", menu=unhide_menu)
        else:
            self._col_menu.add_command(label="(no hidden columns)", state="disabled")
        self._col_menu.add_separator()
        self._col_menu.add_command(
            label="⚙  Manage All Columns…",
            command=self.hide_show_columns
        )

        self._col_menu.tk_popup(event.x_root, event.y_root)

    def _quick_hide_column(self, col_name):
        """Quickly hide a single column via right-click."""
        self.hidden_columns.add(col_name)
        self._setup_columns()
        self._render_page()

    def _quick_unhide_column(self, col_name):
        """Quickly unhide a single column via right-click."""
        self.hidden_columns.discard(col_name)
        self._setup_columns()
        self._render_page()

    def _quick_delete_column(self, col_name):
        """Quickly delete a single column via right-click."""
        if not messagebox.askyesno(
            "Confirm Delete",
            f"Permanently delete column '{col_name}'?\n\n"
            "This cannot be undone."
        ):
            return
        if col_name in self.df_original.columns:
            self.df_original.drop(columns=[col_name], inplace=True)
        if col_name in self.df_display.columns:
            self.df_display.drop(columns=[col_name], inplace=True)
        self.hidden_columns.discard(col_name)
        self._setup_columns()
        self._refresh_filter_cols()
        self._paginate_and_show()
        self._auto_save()
        messagebox.showinfo("Deleted", f"Column '{col_name}' has been deleted.")

    def hide_show_columns(self):
        """Open a popup to manage column visibility (hide/show)."""
        if self.df_original is None:
            messagebox.showwarning("No Data", "Please load a file first.")
            return

        popup = tk.Toplevel(self)
        popup.title("👁  Hide / Show Columns")
        popup.configure(bg="#1a1a2e")
        popup.geometry("520x620")
        popup.grab_set()

        tk.Label(popup,
                 text="👁  Column Visibility Manager",
                 font=("Segoe UI", 13, "bold"), fg="#e94560", bg="#1a1a2e"
                 ).pack(padx=20, pady=(14, 2), anchor="w")

        tk.Label(popup,
                 text="Uncheck columns to hide them from the table.\n"
                      "Hidden columns are NOT deleted — data is preserved.",
                 font=("Segoe UI", 9), fg="#a8b2d8", bg="#1a1a2e",
                 justify="left"
                 ).pack(padx=20, pady=(0, 10), anchor="w")

        # Quick actions frame
        quick_frame = tk.Frame(popup, bg="#1a1a2e")
        quick_frame.pack(fill="x", padx=20, pady=(0, 6))

        all_cols = list(self.df_display.columns)
        check_vars = {}

        def select_all():
            for var in check_vars.values():
                var.set(True)

        def deselect_all():
            for var in check_vars.values():
                var.set(False)

        self._make_btn(quick_frame, "✅ Show All", select_all, "#0f6e56",
                       font=("Segoe UI", 9, "bold"), padx=10, pady=3).pack(side="left", padx=4)
        self._make_btn(quick_frame, "⬜ Hide All", deselect_all, "#555",
                       font=("Segoe UI", 9, "bold"), padx=10, pady=3).pack(side="left", padx=4)

        hidden_count_lbl = tk.Label(quick_frame,
                                     text=f"{len(self.hidden_columns)} column(s) hidden",
                                     fg="#f39c12", bg="#1a1a2e",
                                     font=("Segoe UI", 9, "bold"))
        hidden_count_lbl.pack(side="right", padx=8)

        # Scrollable checkbox list
        list_frame = tk.Frame(popup, bg="#1a1a2e")
        list_frame.pack(fill="both", expand=True, padx=20, pady=4)

        canvas = tk.Canvas(list_frame, bg="#1a1a2e", highlightthickness=0)
        scroll = ttk.Scrollbar(list_frame, orient="vertical", command=canvas.yview)
        inner_frame = tk.Frame(canvas, bg="#1a1a2e")
        inner_frame.bind("<Configure>",
                         lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=inner_frame, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

        # Mouse wheel scrolling
        def _on_mousewheel(event):
            canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        canvas.bind_all("<MouseWheel>", _on_mousewheel)

        for i, col in enumerate(all_cols):
            var = tk.BooleanVar(value=(col not in self.hidden_columns))
            check_vars[col] = var

            row_bg = "#1f1f3a" if i % 2 == 0 else "#1a1a2e"
            row_frame = tk.Frame(inner_frame, bg=row_bg)
            row_frame.pack(fill="x", pady=1)

            cb = tk.Checkbutton(
                row_frame, text=col, variable=var,
                bg=row_bg, fg="#a8b2d8", selectcolor="#0f3460",
                activebackground=row_bg, activeforeground="#e94560",
                font=("Segoe UI", 10), cursor="hand2",
                anchor="w"
            )
            cb.pack(side="left", padx=10, pady=2, fill="x", expand=True)

            # Show a badge if column is currently hidden
            if col in self.hidden_columns:
                tk.Label(row_frame, text="HIDDEN", fg="#f39c12", bg=row_bg,
                         font=("Segoe UI", 8, "bold")).pack(side="right", padx=10)

        # Buttons
        btn_frame = tk.Frame(popup, bg="#1a1a2e")
        btn_frame.pack(pady=12)

        def apply_visibility():
            self.hidden_columns.clear()
            for col, var in check_vars.items():
                if not var.get():
                    self.hidden_columns.add(col)
            self._setup_columns()
            self._render_page()
            # Unbind mousewheel before closing
            canvas.unbind_all("<MouseWheel>")
            popup.destroy()
            hidden_n = len(self.hidden_columns)
            if hidden_n:
                messagebox.showinfo("Columns Hidden",
                                    f"{hidden_n} column(s) are now hidden.\n"
                                    "Use 'Hide/Show Columns' or right-click a header to unhide.")

        self._make_btn(btn_frame, "✅  Apply", apply_visibility, "#0f6e56",
                       padx=14, pady=6).pack(side="left", padx=6)
        self._make_btn(btn_frame, "❌  Cancel",
                       lambda: (canvas.unbind_all("<MouseWheel>"), popup.destroy()),
                       "#555", padx=14, pady=6).pack(side="left", padx=6)

    def delete_columns(self):
        """Open a popup to permanently delete one or more columns."""
        if self.df_original is None:
            messagebox.showwarning("No Data", "Please load a file first.")
            return

        popup = tk.Toplevel(self)
        popup.title("🗑  Delete Columns")
        popup.configure(bg="#1a1a2e")
        popup.geometry("520x620")
        popup.grab_set()

        tk.Label(popup,
                 text="🗑  Delete Columns Permanently",
                 font=("Segoe UI", 13, "bold"), fg="#e94560", bg="#1a1a2e"
                 ).pack(padx=20, pady=(14, 2), anchor="w")

        tk.Label(popup,
                 text="⚠  Select columns to permanently remove from the data.\n"
                      "This action CANNOT be undone!",
                 font=("Segoe UI", 9), fg="#f87171", bg="#1a1a2e",
                 justify="left"
                 ).pack(padx=20, pady=(0, 10), anchor="w")

        all_cols = list(self.df_original.columns)
        check_vars = {}

        # Scrollable checkbox list
        list_frame = tk.Frame(popup, bg="#1a1a2e")
        list_frame.pack(fill="both", expand=True, padx=20, pady=4)

        canvas = tk.Canvas(list_frame, bg="#1a1a2e", highlightthickness=0)
        scroll = ttk.Scrollbar(list_frame, orient="vertical", command=canvas.yview)
        inner_frame = tk.Frame(canvas, bg="#1a1a2e")
        inner_frame.bind("<Configure>",
                         lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=inner_frame, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

        # Mouse wheel scrolling
        def _on_mousewheel(event):
            canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        canvas.bind_all("<MouseWheel>", _on_mousewheel)

        selected_lbl = tk.Label(popup, text="0 column(s) selected for deletion",
                                 fg="#f87171", bg="#1a1a2e",
                                 font=("Segoe UI", 10, "bold"))
        selected_lbl.pack(padx=20, pady=(4, 0), anchor="w")

        def update_count(*args):
            count = sum(1 for v in check_vars.values() if v.get())
            selected_lbl.config(text=f"{count} column(s) selected for deletion")

        for i, col in enumerate(all_cols):
            var = tk.BooleanVar(value=False)
            var.trace_add("write", update_count)
            check_vars[col] = var

            row_bg = "#2d1a1a" if i % 2 == 0 else "#1a1a2e"
            row_frame = tk.Frame(inner_frame, bg=row_bg)
            row_frame.pack(fill="x", pady=1)

            cb = tk.Checkbutton(
                row_frame, text=col, variable=var,
                bg=row_bg, fg="#a8b2d8", selectcolor="#3d1a1a",
                activebackground=row_bg, activeforeground="#f87171",
                font=("Segoe UI", 10), cursor="hand2",
                anchor="w"
            )
            cb.pack(side="left", padx=10, pady=2, fill="x", expand=True)

        # Buttons
        btn_frame = tk.Frame(popup, bg="#1a1a2e")
        btn_frame.pack(pady=12)

        def do_delete():
            to_delete = [col for col, var in check_vars.items() if var.get()]
            if not to_delete:
                messagebox.showwarning("Nothing Selected",
                                       "Please check at least one column to delete.",
                                       parent=popup)
                return
            confirm = messagebox.askyesno(
                "⚠  Confirm Deletion",
                f"Permanently delete {len(to_delete)} column(s)?\n\n"
                + "\n".join(f"  • {c}" for c in to_delete) +
                "\n\nThis cannot be undone!",
                parent=popup
            )
            if not confirm:
                return

            for col in to_delete:
                if col in self.df_original.columns:
                    self.df_original.drop(columns=[col], inplace=True)
                if col in self.df_display.columns:
                    self.df_display.drop(columns=[col], inplace=True)
                self.hidden_columns.discard(col)

            self._setup_columns()
            self._refresh_filter_cols()
            self._paginate_and_show()
            self._auto_save()
            canvas.unbind_all("<MouseWheel>")
            popup.destroy()
            messagebox.showinfo("Deleted",
                                f"{len(to_delete)} column(s) deleted successfully.")

        self._make_btn(btn_frame, "🗑  Delete Selected", do_delete, "#c0392b",
                       padx=14, pady=6).pack(side="left", padx=6)
        self._make_btn(btn_frame, "❌  Cancel",
                       lambda: (canvas.unbind_all("<MouseWheel>"), popup.destroy()),
                       "#555", padx=14, pady=6).pack(side="left", padx=6)

    # ── ADD / DELETE / EDIT ──────────────────────────────

    def add_row(self, position="below"):
        if self.df_original is None:
            messagebox.showwarning("No Data", "Please load a file first.")
            return

        insert_idx = None
        selected = self.tree.selection()
        orig_idx = None
        if selected:
            item = selected[0]
            children = self.tree.get_children()
            pos_in_page = list(children).index(item)
            start = self.current_page * PAGE_SIZE
            df_idx = self.df_display.index[start + pos_in_page]
            orig_idx = df_idx
            if position == "above":
                insert_idx = orig_idx
            else:
                insert_idx = orig_idx + 1

        pos_label = f" ({position} row {orig_idx})" if insert_idx is not None else " (at end)"

        cols = list(self.df_original.columns)
        win = tk.Toplevel(self)
        win.title(f"Insert New Row{pos_label}")
        win.configure(bg="#1a1a2e")
        win.geometry("500x600")

        tk.Label(
            win, text=f"📝 New row will be inserted {position} the selected row" if selected
                      else "📝 New row will be added at the end",
            font=("Segoe UI", 10, "bold"), fg="#e94560", bg="#1a1a2e"
        ).pack(padx=16, pady=(10, 4))

        entries = {}
        canvas = tk.Canvas(win, bg="#1a1a2e")
        scroll = ttk.Scrollbar(win, orient="vertical", command=canvas.yview)
        frame  = tk.Frame(canvas, bg="#1a1a2e")
        frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=frame, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side="left", fill="both", expand=True, padx=10, pady=10)
        scroll.pack(side="right", fill="y")

        for i, col in enumerate([c for c in cols if not c.startswith("_")]):
            tk.Label(frame, text=col, fg="#a8b2d8", bg="#1a1a2e",
                     font=("Segoe UI", 9)).grid(row=i, column=0, sticky="w", pady=2, padx=5)
            e = tk.Entry(frame, width=30, bg="#0f3460", fg="white",
                         insertbackground="white", font=("Segoe UI", 9))
            e.grid(row=i, column=1, pady=2, padx=5)
            entries[col] = e

        def save():
            new_row = {col: entries[col].get() for col in entries}
            new_df = pd.DataFrame([new_row])
            if insert_idx is not None and 0 <= insert_idx <= len(self.df_original):
                upper = self.df_original.iloc[:insert_idx]
                lower = self.df_original.iloc[insert_idx:]
                self.df_original = pd.concat([upper, new_df, lower], ignore_index=True)
            else:
                self.df_original = pd.concat(
                    [self.df_original, new_df], ignore_index=True)
            self.df_display = self.df_original.copy()
            self._setup_columns()
            self._paginate_and_show()
            self._auto_save()
            win.destroy()
            messagebox.showinfo("Done", f"Row inserted {position} successfully!")

        self._make_btn(win, "💾 Save Row", save, "#e94560").pack(pady=10)

    def delete_row(self):
        selected = self.tree.selection()
        if not selected:
            messagebox.showwarning("Select Rows", "Please select rows to delete.")
            return
        if not messagebox.askyesno("Confirm", f"Delete {len(selected)} row(s)?"):
            return
        start = self.current_page * PAGE_SIZE
        idxs_to_drop = []
        children = self.tree.get_children()
        for sel in selected:
            pos = children.index(sel)
            df_idx = self.df_display.index[start + pos]
            idxs_to_drop.append(df_idx)

        self.df_original.drop(index=idxs_to_drop, inplace=True)
        self.df_original.reset_index(drop=True, inplace=True)
        self.df_display = self.df_original.copy()
        self._paginate_and_show()
        self._auto_save()

    def edit_cell(self):
        selected = self.tree.selection()
        if not selected:
            messagebox.showwarning("Select", "Please select a row.")
            return
        item = selected[0]
        cols = list(self.tree["columns"])

        win = tk.Toplevel(self)
        win.title("Edit Row")
        win.configure(bg="#1a1a2e")
        win.geometry("500x600")

        canvas = tk.Canvas(win, bg="#1a1a2e")
        scroll = ttk.Scrollbar(win, orient="vertical", command=canvas.yview)
        frame  = tk.Frame(canvas, bg="#1a1a2e")
        frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=frame, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side="left", fill="both", expand=True, padx=10, pady=10)
        scroll.pack(side="right", fill="y")

        current_vals = self.tree.item(item, "values")
        entries = {}
        row_num = 0
        for i, col in enumerate(cols):
            if col.startswith("_"): continue
            tk.Label(frame, text=col, fg="#a8b2d8", bg="#1a1a2e",
                     font=("Segoe UI", 9)).grid(row=row_num, column=0, sticky="w", pady=2, padx=5)
            e = tk.Entry(frame, width=30, bg="#0f3460", fg="white",
                         insertbackground="white", font=("Segoe UI", 9))
            e.insert(0, current_vals[i] if i < len(current_vals) else "")
            e.grid(row=row_num, column=1, pady=2, padx=5)
            entries[col] = e
            row_num += 1

        def _convert_value(val_str, col_name, df):
            """Convert a string value to match the column's dtype."""
            if val_str.strip() == "":
                return np.nan
            try:
                col_dtype = df[col_name].dtype
                if pd.api.types.is_float_dtype(col_dtype):
                    return float(val_str)
                elif pd.api.types.is_integer_dtype(col_dtype):
                    return int(float(val_str))
                elif pd.api.types.is_bool_dtype(col_dtype):
                    return val_str.lower() in ("true", "1", "yes")
            except (ValueError, TypeError):
                pass
            return val_str

        def save_edit():
            children = self.tree.get_children()
            pos = children.index(item)
            start = self.current_page * PAGE_SIZE
            display_idx = start + pos
            # Get the original DataFrame index (not page position)
            if display_idx < len(self.df_display):
                df_idx = self.df_display.index[display_idx]
            else:
                messagebox.showerror("Error", "Row index out of range.", parent=win)
                return
            for col, entry in entries.items():
                raw_val = entry.get()
                # Convert to the correct dtype before assignment
                if df_idx in self.df_original.index and col in self.df_original.columns:
                    converted = _convert_value(raw_val, col, self.df_original)
                    self.df_original.at[df_idx, col] = converted
                if df_idx in self.df_display.index and col in self.df_display.columns:
                    converted = _convert_value(raw_val, col, self.df_display)
                    self.df_display.at[df_idx, col] = converted
            self._render_page()
            self._auto_save()
            win.destroy()
            messagebox.showinfo("Saved", "Row updated!")

        self._make_btn(win, "💾 Save Changes", save_edit, "#e94560").pack(pady=10)

    # ── BULK EDIT ─────────────────────────────────────────

    def bulk_edit(self):
        if self.df_original is None:
            messagebox.showwarning("No Data", "Please load a file first.")
            return
        if self.df_display is None or len(self.df_display) == 0:
            messagebox.showwarning("No Data", "No data is currently displayed.")
            return

        popup = tk.Toplevel(self)
        popup.title("Bulk Edit Column")
        popup.configure(bg="#1a1a2e")
        popup.geometry("520x400")
        popup.grab_set()

        tk.Label(popup, text="⚡ Bulk Edit — Update All Filtered Rows",
                 font=("Segoe UI", 11, "bold"), fg="#e94560", bg="#1a1a2e"
                 ).pack(padx=16, pady=(16, 4))

        n_rows = len(self.df_display)
        tk.Label(popup, text=f"Currently {n_rows:,} rows visible (filtered data)",
                 font=("Segoe UI", 10), fg="#a8b2d8", bg="#1a1a2e",
                 justify="left").pack(padx=16, pady=(0, 12), anchor="w")

        frm1 = tk.Frame(popup, bg="#1a1a2e")
        frm1.pack(fill="x", padx=20, pady=4)
        tk.Label(frm1, text="Select column:", fg="#a8b2d8", bg="#1a1a2e",
                 font=("Segoe UI", 10), width=18, anchor="w").pack(side="left")
        visible_cols = [c for c in self.df_display.columns if not c.startswith("_")]
        col_var = ttk.Combobox(frm1, values=visible_cols, state="readonly",
                               font=("Segoe UI", 10), width=24)
        col_var.pack(side="left", padx=6)
        if visible_cols:
            col_var.set(visible_cols[0])

        frm2 = tk.Frame(popup, bg="#1a1a2e")
        frm2.pack(fill="x", padx=20, pady=4)
        tk.Label(frm2, text="Value to fill:", fg="#a8b2d8", bg="#1a1a2e",
                 font=("Segoe UI", 10), width=18, anchor="w").pack(side="left")
        val_entry = tk.Entry(frm2, width=26, bg="#0f3460", fg="white",
                             insertbackground="white", font=("Segoe UI", 10))
        val_entry.pack(side="left", padx=6)

        frm3 = tk.Frame(popup, bg="#1a1a2e")
        frm3.pack(fill="x", padx=20, pady=8)
        tk.Label(frm3, text="Apply to:", fg="#a8b2d8", bg="#1a1a2e",
                 font=("Segoe UI", 10), width=18, anchor="w").pack(side="left")
        scope_var = tk.StringVar(value="filtered")
        tk.Radiobutton(frm3, text=f"Filtered rows ({n_rows:,})",
                       variable=scope_var, value="filtered",
                       bg="#1a1a2e", fg="white", selectcolor="#533483",
                       font=("Segoe UI", 9)).pack(side="left", padx=4)
        tk.Radiobutton(frm3, text=f"All rows ({len(self.df_original):,})",
                       variable=scope_var, value="all",
                       bg="#1a1a2e", fg="white", selectcolor="#533483",
                       font=("Segoe UI", 9)).pack(side="left", padx=4)

        preview_lbl = tk.Label(popup, text="", fg="#4ade80", bg="#1a1a2e",
                                font=("Segoe UI", 9), justify="left")
        preview_lbl.pack(padx=20, pady=4, anchor="w")

        def update_preview(*args):
            col = col_var.get()
            val = val_entry.get()
            scope = scope_var.get()
            count = n_rows if scope == "filtered" else len(self.df_original)
            preview_lbl.config(text=f"Will set '{col}' → '{val}' for {count:,} rows")

        col_var.bind("<<ComboboxSelected>>", update_preview)
        val_entry.bind("<KeyRelease>", update_preview)
        scope_var.trace_add("write", update_preview)

        btn_frame = tk.Frame(popup, bg="#1a1a2e")
        btn_frame.pack(pady=16)

        def apply_bulk():
            col = col_var.get()
            val = val_entry.get()
            scope = scope_var.get()
            if not col:
                messagebox.showwarning("Select Column", "Please select a column.", parent=popup)
                return
            confirm = messagebox.askyesno(
                "Confirm",
                f"Column: '{col}'\nValue: '{val}'\nRows: {n_rows if scope=='filtered' else len(self.df_original):,}\n\nProceed?",
                parent=popup
            )
            if not confirm: return

            if scope == "filtered":
                idxs = self.df_display.index.tolist()
                self.df_original.loc[idxs, col] = val
                self.df_display.loc[idxs, col]  = val
            else:
                self.df_original[col] = val
                self.df_display[col]  = val

            self._render_page()
            self._auto_save()
            popup.destroy()
            messagebox.showinfo("Done", f"'{col}' updated successfully!")

        self._make_btn(btn_frame, "✅ Apply", apply_bulk, "#0f6e56").pack(side="left", padx=8)
        self._make_btn(btn_frame, "❌ Cancel", popup.destroy, "#555").pack(side="left", padx=8)


    # ── EXPORT ───────────────────────────────────────────

    def export(self):
        if self.df_display is None:
            messagebox.showwarning("No Data", "Nothing to export.")
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".xlsx",
            filetypes=[("Excel", "*.xlsx"), ("CSV", "*.csv")],
            title="Export Results"
        )
        if not path: return

        self.lbl_file.config(text=f"⏳ Exporting to {os.path.basename(path)}...")
        self.update_idletasks()

        def _do_export():
            try:
                df_export = self.df_display[[c for c in self.df_display.columns if not c.startswith("_matched")]]
                if path.endswith(".csv"):
                    df_export.to_csv(path, index=False)
                else:
                    self._export_styled_excel(df_export, path)
                self.after(0, lambda: self._on_export_done(path))
            except Exception as e:
                import traceback
                err = f"{e}\n\n{traceback.format_exc()}"
                self.after(0, lambda: self._on_export_error(err))

        threading.Thread(target=_do_export, daemon=True).start()

    def _on_export_done(self, path):
        self.lbl_file.config(text=f"✅ Exported: {os.path.basename(path)}")
        messagebox.showinfo("Exported", f"File saved:\n{path}")

    def _on_export_error(self, err):
        self.lbl_file.config(text="❌ Export failed!")
        messagebox.showerror("Export Error", err)

    def _export_styled_excel(self, df_export, path):
        """Export to Excel with row colours matching the tool's UI."""
        from openpyxl import Workbook
        from openpyxl.styles import Font, PatternFill, Alignment, Border, Side

        wb = Workbook()
        ws = wb.active
        ws.title = "Reconciliation"

        # ── Colour definitions (matching the tool's UI highlights) ─────
        header_fill = PatternFill(start_color="0F3460", end_color="0F3460", fill_type="solid")
        header_font = Font(name="Segoe UI", bold=True, color="E94560", size=10)

        # ✅ Matched (1:1) → light green
        matched_fill = PatternFill(start_color="D5F5E3", end_color="D5F5E3", fill_type="solid")
        matched_font = Font(name="Segoe UI", color="1A6B3C", size=10)

        # 📊 Consecutive Match → light blue
        consec_fill  = PatternFill(start_color="D6EAF8", end_color="D6EAF8", fill_type="solid")
        consec_font  = Font(name="Segoe UI", color="1A4D8E", size=10)

        # 🧮 Sum Match → light purple
        sum_fill     = PatternFill(start_color="E8DAEF", end_color="E8DAEF", fill_type="solid")
        sum_font     = Font(name="Segoe UI", color="6C3483", size=10)

        # 🔄 Cross Matched → light yellow
        cross_fill   = PatternFill(start_color="FEF9E7", end_color="FEF9E7", fill_type="solid")
        cross_font   = Font(name="Segoe UI", color="7D6608", size=10)

        # ❌ Unmatched → light red
        unmatched_fill = PatternFill(start_color="FADBD8", end_color="FADBD8", fill_type="solid")
        unmatched_font = Font(name="Segoe UI", color="922B21", size=10)

        default_font = Font(name="Segoe UI", size=10)
        thin_border  = Border(
            left=Side(style="thin", color="CCCCCC"),
            right=Side(style="thin", color="CCCCCC"),
            top=Side(style="thin", color="CCCCCC"),
            bottom=Side(style="thin", color="CCCCCC"),
        )

        cols = list(df_export.columns)

        # Find _status column index within the export columns
        status_col_idx = None
        for i, c in enumerate(cols):
            if c == "_status":
                status_col_idx = i
                break

        # ── Write headers ────────────────────────────────────────────────
        for col_idx, col_name in enumerate(cols, 1):
            cell = ws.cell(row=1, column=col_idx, value=col_name)
            cell.fill = header_fill
            cell.font = header_font
            cell.alignment = Alignment(horizontal="center")
            cell.border = thin_border

        # ── Write data rows with conditional formatting ──────────────────
        total_rows = len(df_export)
        for row_idx, (_, row) in enumerate(df_export.iterrows(), 2):
            # Progress update every 500 rows
            if (row_idx - 2) % 500 == 0:
                self.after(0, lambda r=row_idx-2: self.lbl_file.config(
                    text=f"⏳ Exporting row {r:,}/{total_rows:,}..."))

            # Determine row status
            status = ""
            if status_col_idx is not None:
                try:
                    val = row.iloc[status_col_idx]
                    status = str(val) if pd.notna(val) else ""
                except Exception:
                    status = ""

            if "Cross" in status:
                row_fill, row_font = cross_fill, cross_font
            elif "Consecutive" in status:
                row_fill, row_font = consec_fill, consec_font
            elif "Sum Match" in status:
                row_fill, row_font = sum_fill, sum_font
            elif "Matched" in status and "Unmatched" not in status:
                row_fill, row_font = matched_fill, matched_font
            elif "Unmatched" in status:
                row_fill, row_font = unmatched_fill, unmatched_font
            else:
                row_fill, row_font = None, default_font

            for col_idx, col_name in enumerate(cols, 1):
                try:
                    value = row[col_name]
                    cell = ws.cell(row=row_idx, column=col_idx,
                                   value=str(value) if pd.notna(value) else "")
                except Exception:
                    cell = ws.cell(row=row_idx, column=col_idx, value="")
                cell.font = row_font
                cell.border = thin_border
                if row_fill:
                    cell.fill = row_fill

        # ── Auto-fit column widths ───────────────────────────────────────
        for col_idx, col_name in enumerate(cols, 1):
            max_len = len(str(col_name))
            # Sample first 50 rows for width estimation
            for r in range(2, min(52, ws.max_row + 1)):
                cell_val = ws.cell(row=r, column=col_idx).value
                if cell_val:
                    max_len = max(max_len, len(str(cell_val)))
            ws.column_dimensions[ws.cell(row=1, column=col_idx).column_letter].width = min(max_len + 3, 40)

        # ── Freeze top row ───────────────────────────────────────────────
        ws.freeze_panes = "A2"

        wb.save(path)

    # ── AUTO-SAVE ─────────────────────────────────────────

    def set_auto_save_path(self):
        """Let user pick a file path for automatic background saving."""
        if self.df_original is None:
            messagebox.showwarning("No Data", "Please load a file first.")
            return

        # If auto-save is already active, offer to change or turn off
        if self.auto_save_path:
            choice = messagebox.askyesnocancel(
                "Auto-Save Active",
                f"Auto-save is currently writing to:\n{self.auto_save_path}\n\n"
                "• Yes → Change the path\n"
                "• No → Turn off auto-save\n"
                "• Cancel → Keep current setting"
            )
            if choice is None:  # Cancel
                return
            if choice is False:  # No → turn off
                self.auto_save_path = ""
                self.lbl_autosave.config(text="")
                messagebox.showinfo("Auto-Save Off", "Auto-save has been turned off.")
                return
            # Yes → fall through to pick new path

        path = filedialog.asksaveasfilename(
            title="Set Auto-Save Path",
            defaultextension=".xlsx",
            filetypes=[("Excel", "*.xlsx"), ("CSV", "*.csv")],
            initialfile="auto_save_reconciliation.xlsx"
        )
        if not path:
            return

        self.auto_save_path = path
        self.lbl_autosave.config(
            text=f"🔄 Auto-save: {os.path.basename(path)}",
            fg="#4ade80"
        )
        # Do an immediate first save
        self._auto_save()
        messagebox.showinfo(
            "Auto-Save Enabled",
            f"All changes will now auto-save to:\n{path}\n\n"
            "Every edit, row/column change, and reconciliation\n"
            "will be saved automatically in the background."
        )

    def _auto_save(self):
        """Save df_original to the auto-save path in a background thread."""
        if not self.auto_save_path or self.df_original is None:
            return

        # Take a snapshot of the data to avoid threading issues
        df_snapshot = self.df_original.copy()
        path = self.auto_save_path
        self.lbl_autosave.config(
            text=f"⏳ Saving to {os.path.basename(path)}...",
            fg="#f39c12"
        )

        def _do_save():
            if not self._auto_save_lock.acquire(blocking=False):
                # Another save is already running — skip this one
                return
            try:
                # Exclude internal columns from export
                export_cols = [c for c in df_snapshot.columns if c != "_matched"]
                df_export = df_snapshot[export_cols]

                if path.lower().endswith(".csv"):
                    df_export.to_csv(path, index=False)
                else:
                    # Use styled export with color highlighting
                    self._export_styled_excel(df_export, path)

                now = datetime.now().strftime("%H:%M:%S")
                self.after(0, lambda: self.lbl_autosave.config(
                    text=f"✅ Auto-saved at {now} → {os.path.basename(path)}",
                    fg="#4ade80"
                ))
            except Exception as e:
                self.after(0, lambda: self.lbl_autosave.config(
                    text=f"❌ Auto-save failed: {e}",
                    fg="#f87171"
                ))
            finally:
                self._auto_save_lock.release()

        threading.Thread(target=_do_save, daemon=True).start()



# ══════════════════════════════════════════════════════════
if __name__ == "__main__":
    app = ReconciliationApp()
    app.mainloop()
