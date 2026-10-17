from __future__ import annotations
import bisect

MSG_BAD = ("Bad pattern: first copy is undefined. Returning E(A,0) (i.e. cut). "
           "Please contact the author (E-mail: qwerasdfyh@126.com) with the previous pattern.")

def _find(a, x):
    i = bisect.bisect_left(a, x)
    return i if i < len(a) and a[i] == x else -1

def _has(a, x): return _find(a, x) >= 0

def _merge_unique_sorted(a, b):
    if not b: return a
    b = sorted(set(b))
    if not a: return b
    out, i, j, na, nb = [], 0, 0, len(a), len(b)
    while i < na and j < nb:
        va, vb = a[i], b[j]
        if va < vb: out.append(va); i += 1
        elif va > vb: out.append(vb); j += 1
        else: out.append(va); i += 1; j += 1
    if i < na: out.extend(a[i:])
    if j < nb: out.extend(b[j:])
    return out

def _shift_vals_gt_inplace(row, k, d):
    if not d: return
    i = bisect.bisect_right(row, k)
    for p in range(i, len(row)): row[p] += d

def _shift_marks_gt(mset, k, d):
    if not d or not mset: return mset
    return {x + d if x > k else x for x in mset}

class Pattern:
    __slots__ = ("rows", "mask")
    def __init__(self, rows, mask=None):
        self.rows = [list(r) for r in rows]
        self.mask = [set() for _ in self.rows] if mask is None else [set(s) for s in mask]
        if self.mask: self.mask[0] = set()

    def clone(self): return Pattern(self.rows, self.mask)
    def is_zero(self): return len(self.rows) == 1 and not self.rows[0]
    def is_succ(self):
        return (not self.is_zero()) and len(self.rows[-1]) == 2 and self.rows[-1][0] == 0

    def cut(self):
        if self.is_zero() or len(self.rows) <= 1: return False
        if not self.rows[0]:
            self.rows, self.mask = [[]], [set()]
            return False
        self.rows[0].pop(); self.rows.pop(); self.mask.pop()
        if len(self.rows) == 1 and not self.rows[0]: self.mask = [set()]
        return True

    def draw(self):
        if self.is_zero(): return
        base, seqs = self.rows[0], self.rows[1:]
        if not seqs: return
        max_len = (max((s[-1] for s in seqs if s), default=-1) + 1)
        for i, seq in enumerate(seqs, start=1):
            if i > len(base) or not seq: continue
            line = [' '] * max_len
            m = self.mask[i]
            for x in seq:
                if 0 <= x < max_len: line[x] = 'a' if x in m else 'o'
            print(''.join(line[:seq[-1] + 1]) + f" {base[i-1]}")

    def to_string(self):
        if self.is_zero(): return ""
        base, out = self.rows[0], []
        for i in range(1, len(self.rows)):
            seq, m = self.rows[i], self.mask[i]
            parts = [f"*{x}" if x in m else str(x) for x in reversed(seq)]
            step = base[i-1] if i-1 < len(base) else 0
            out.append("(" + ",".join(parts) + ")" + str(step))
        return "".join(out)

def _tr(pat: Pattern, i: int, k1: int):
    L = pat.rows[0][i-1]; row = pat.rows[i]
    if k1 <= L: return None
    j = row[k1-1]; thr = row[k1-L-1]
    seq, cur = [j], j
    while cur > thr:
        if cur <= 0 or cur >= len(pat.rows): return None
        Lc = pat.rows[0][cur-1]; rc = pat.rows[cur]
        if len(rc) < Lc + 1: return None
        cur = rc[-Lc-1]; seq.append(cur)
        if len(seq) > 200000: return None
    return seq if cur == thr else None

def _f(A: Pattern):
    n = len(A.rows) - 1
    base, last = A.rows[0], A.rows[n]
    Ln = base[n-1]; pn = last[-Ln-1]; a1 = last[0]
    def f(x):
        if x < a1: return x
        if x >= pn: return x + (n - pn)
        i = _find(last, x)
        if i < 0: return None
        j = i + Ln
        return None if j >= len(last) else last[j]
    return f, n, base, last, Ln, pn, a1

def _copy_mark_filter(A, pn, a1, last, Ln, src_i, src_L, src_row, dst_row, dst_marks, pre):
    if not dst_marks: return dst_marks
    kept = set()
    for x_dst in dst_marks:
        y_src = pre.get(x_dst)
        if y_src is None: continue
        ksrc = _find(src_row, y_src)
        if ksrc < 0: continue
        tr = _tr(A, src_i, ksrc + 1)
        if not tr or len(tr) < 2: continue
        if tr[-2] >= pn: kept.add(x_dst); continue
        y0 = next((t for t in tr if t < pn), None)
        if y0 is None or y0 < a1: kept.add(x_dst); continue
        j = _find(last, y0)
        if j < 0: continue
        jj = j + Ln
        if jj >= len(last): continue
        if last[jj] in A.mask[len(A.rows) - 1]:
            q = _find(dst_row, x_dst)
            if q < 0: continue
            check_pos = (q + 1) - src_L
            if check_pos >= 1 and dst_row[check_pos - 1] <= a1:
                kept.add(x_dst)
    return kept

def _copy_full(A: Pattern):
    f, n, base, last, Ln, pn, a1 = _f(A)
    new_base = base[:n-1] + base[pn-1:n]
    new_rows, new_mask = [new_base], [set()]
    for i in range(1, n):
        new_rows.append(A.rows[i][:]); new_mask.append(set(A.mask[i]))
    for src_i in range(pn, n+1):
        src_row = A.rows[src_i]
        dst_row = [f(x) for x in src_row]
        if any(v is None for v in dst_row): raise RuntimeError("copy undefined")
        dst_row = sorted(set(dst_row))
        dst_marks, pre = set(), {}
        for y_src in A.mask[src_i]:
            x_dst = f(y_src)
            if x_dst is None: raise RuntimeError("copy undefined")
            dst_marks.add(x_dst); pre[x_dst] = y_src
        dst_marks = _copy_mark_filter(A, pn, a1, last, Ln, src_i, base[src_i-1], src_row, dst_row, dst_marks, pre)
        new_rows.append(dst_row); new_mask.append(dst_marks)
    return Pattern(new_rows, new_mask)

def _copy_one_top_row_replace_last(A: Pattern):
    f, n, base, last, Ln, pn, a1 = _f(A)
    B = A.clone(); B.cut()
    src_i = pn
    src_row = A.rows[src_i]
    dst_row = [f(x) for x in src_row]
    if any(v is None for v in dst_row): raise RuntimeError("copy undefined")
    dst_row = sorted(set(dst_row))
    B.rows[0].append(base[src_i-1])
    dst_marks, pre = set(), {}
    for y_src in A.mask[src_i]:
        x_dst = f(y_src)
        if x_dst is None: raise RuntimeError("copy undefined")
        dst_marks.add(x_dst); pre[x_dst] = y_src
    dst_marks = _copy_mark_filter(A, pn, a1, last, Ln, src_i, base[src_i-1], src_row, dst_row, dst_marks, pre)
    B.rows.append(dst_row); B.mask.append(dst_marks)
    return B

def _mark_completion(B: Pattern, r: int, record: dict):
    row0 = B.rows[r]
    marked = sorted(x for x in B.mask[r] if _has(row0, x))
    if not marked: return
    for b in marked:
        row = B.rows[r]
        kb = _find(row, b)
        trb = _tr(B, r, kb + 1) if kb >= 0 else None
        if not trb or len(trb) < 2: continue
        t = trb[-2]; s = record.get(t)
        if not s: continue
        ok = True
        for j in range(3, len(trb)+1):
            need = trb[-j+1] + 1
            rr = trb[-j]
            if rr <= 0 or rr >= len(B.rows) or not _has(B.rows[rr], need):
                ok = False; break
        if not ok: continue
        add_s = list(s)
        add_m = list(range(b+1, b+len(s)+1))
        B.rows[r] = _merge_unique_sorted(B.rows[r], add_s + add_m)
        B.mask[r].difference_update(add_s)
        B.mask[r].update(add_m)
        B.rows[0][r-1] += len(s)

def _native_completion(B: Pattern, r: int, record: dict):
    base = B.rows[0]; Lr = base[r-1]; row_r = B.rows[r]
    if len(row_r) > 2 * Lr: return 0
    pr = row_r[-Lr-1]; a = row_r[-Lr]
    s, cur = [], a
    while True:
        nxt = B.rows[cur][-2]
        if nxt <= pr: break
        s.append(nxt); cur = nxt
    t = len(s)
    if not t: return 0
    record[r] = s[:]
    for i in range(r+1, len(B.rows)):
        _shift_vals_gt_inplace(B.rows[i], r, t)
        B.mask[i] = _shift_marks_gt(B.mask[i], r, t)
    record2 = {}
    for k, v in record.items():
        nk = k + t if k > r else k
        record2[nk] = [x + t if x > r else x for x in v]
    record.clear(); record.update(record2)
    s2 = [x + t if x > r else x for x in s]
    old_row, old_marks, old_L = B.rows[r][:], set(B.mask[r]), base[r-1]
    mid = (len(old_row) == 2 * old_L)
    base[r-1:r-1] = [0] * t
    B.rows[r+1:r+1] = [[] for _ in range(t)]
    B.mask[r+1:r+1] = [set() for _ in range(t)]
    row_t = _merge_unique_sorted(old_row, s2 + list(range(r+1, r+t+1)))
    marks_t = set(old_marks)
    marks_t.update(range(r, r+t))
    marks_t.discard(r+t)
    marks_t.difference_update(s2)
    rows_seg = [None] * (t+1); marks_seg = [None] * (t+1); steps_seg = [None] * (t+1)
    rows_seg[t], marks_seg[t], steps_seg[t] = row_t, marks_t, old_L + t
    start_i = t
    if mid:
        rows_seg[t-1] = [x for x in rows_seg[t] if x != (r+t)]
        marks_seg[t-1] = set(marks_seg[t]); marks_seg[t-1].discard(r+t-1)
        steps_seg[t-1] = steps_seg[t]
        start_i = t-1
    for i in range(start_i, 0, -1):
        cur_row, cur_marks, cur_L = rows_seg[i], marks_seg[i], steps_seg[i]
        x1 = r + i
        tmp = [x for x in cur_row if x != x1]
        tmp_marks = set(cur_marks); tmp_marks.discard(x1)
        if not (mid and i == t):
            x2 = cur_row[-cur_L]
            tmp = [x for x in tmp if x != x2]
            tmp_marks.discard(x2)
            nxt_L = cur_L - 1
        else:
            nxt_L = cur_L
        tmp_marks.discard(r+i-1)
        rows_seg[i-1], marks_seg[i-1], steps_seg[i-1] = tmp, tmp_marks, nxt_L
    for j in range(t+1):
        B.rows[r+j] = rows_seg[j]
        B.mask[r+j] = marks_seg[j]
        base[r+j-1] = steps_seg[j]
    return t

def _expand_E(A: Pattern, m: int, silent=False):
    if A.is_zero() or A.is_succ():
        B = A.clone(); B.cut(); return B, 0
    if m == 0:
        B = A.clone(); B.cut(); return B, 0
    n0 = len(A.rows) - 1
    try:
        B = _copy_full(A)
    except Exception:
        if not silent: print(MSG_BAD)
        C = A.clone(); C.cut(); return C, 0
    for _ in range(m-1):
        B = _copy_full(B)
    B.cut()
    record = {}
    r = n0
    while r <= len(B.rows) - 1:
        _mark_completion(B, r, record)
        t = _native_completion(B, r, record)
        r += t + 1
    return B, m + 1

def _apply_one(A: Pattern, silent=False):
    if A.is_zero() or A.is_succ():
        B = A.clone(); B.cut(); return B, 0
    n = len(A.rows) - 1
    try:
        B = _copy_one_top_row_replace_last(A)
    except Exception:
        if not silent: print(MSG_BAD)
        C = A.clone(); C.cut(); return C, 0
    record = {}
    t = _native_completion(B, n, record)
    for _ in range(t): B.cut()
    return B, 1

initial_rows = [
    [1, 1, 2, 2, 2],
    [0, 1],
    [0, 1, 2],
    [0, 1, 2, 3],
    [0, 1, 2, 3, 4],
    [2, 3, 4, 5],
]
initial_mask = [set() for _ in initial_rows]
initial_mask[4] = {3}


def _cmp_lists(a, b):
    m = min(len(a), len(b))
    for i in range(m):
        if a[i] < b[i]: return -1
        if a[i] > b[i]: return 1
    return -1 if len(a) < len(b) else (1 if len(a) > len(b) else 0)

def _row_key(pat: Pattern, row_idx: int):
    base, row = pat.rows[0], pat.rows[row_idx]
    l = base[row_idx-1] if row_idx-1 < len(base) else 0
    keep = row[:] if l <= 1 else (row[:] if len(row) < l else [row[0]] + row[l:])
    keep.reverse()
    return keep

def compare_patterns(a: Pattern, b: Pattern):
    ra, rb = len(a.rows)-1, len(b.rows)-1
    for i in range(1, min(ra, rb)+1):
        c = _cmp_lists(_row_key(a, i), _row_key(b, i))
        if c: return c
    return -1 if ra < rb else (1 if ra > rb else 0)

def _is_prefix(seg: Pattern, full: Pattern):
    if len(seg.rows) > len(full.rows): return False
    if seg.rows[0] != full.rows[0][:len(seg.rows[0])]: return False
    for i in range(1, len(seg.rows)):
        if seg.rows[i] != full.rows[i]: return False
    return True

def _is_proper_prefix(seg: Pattern, full: Pattern):
    return _is_prefix(seg, full) and (len(seg.rows) < len(full.rows))

def _apply_number(pat: Pattern, n: int, silent=False):
    if pat.is_zero(): return pat.clone(), 0
    if n == 0 or pat.is_succ():
        q = pat.clone(); q.cut(); return q, 0
    if n == 1: return _apply_one(pat, silent=silent)
    B, ok = _expand_E(pat, n-1, silent=silent)
    return (B, 0) if ok == 0 else (B, n)

def reconstruct_pattern_list(op_numbers, silent=False):
    pats = [Pattern(initial_rows, initial_mask)]
    executed = []
    for n in op_numbers:
        nxt, actual = _apply_number(pats[-1], n, silent=silent)
        executed.append(actual); pats.append(nxt)
    return executed, pats, None

def _pattern_equal(a: Pattern, b: Pattern): return a.rows == b.rows and a.mask == b.mask

def _pattern_sig(p: Pattern):
    return (tuple(tuple(r) for r in p.rows), tuple(tuple(sorted(s)) for s in p.mask))

_EXPAND_COUNTS_CACHE = {}

def _expand_row_counts_from(start_pat: Pattern, n: int):
    key = (_pattern_sig(start_pat), n)
    if key in _EXPAND_COUNTS_CACHE: return _EXPAND_COUNTS_CACHE[key][:]
    counts = [len(start_pat.rows)]
    for k in range(1, n+1):
        res, _ = _apply_number(start_pat, k, silent=True)
        counts.append(len(res.rows))
    _EXPAND_COUNTS_CACHE[key] = counts[:]
    return counts

def _simplify(op_numbers, pattern_list):
    target = pattern_list[-1].clone()
    s = reconstruct_pattern_list(op_numbers, silent=True)[0]
    pattern_list = reconstruct_pattern_list(s, silent=True)[1]
    i = len(s) - 1
    while i >= 0:
        if i >= len(s): i = len(s)-1
        if i < 0: break
        if s[i] == 0: i -= 1; continue
        while True:
            if i >= len(s): break
            n = s[i]
            if n <= 0: break
            j, z = i+1, 0
            while j < len(s) and s[j] == 0: z += 1; j += 1
            if n == 1:
                if z < 1: break
                cand = s[:i] + s[i+1:]
            else:
                start_pat = pattern_list[i]
                counts = _expand_row_counts_from(start_pat, n)
                need = counts[n] - counts[n-1]
                if need < 0: need = 0
                if z < need: break
                cand = s[:]
                cand[i] = n-1
                if need: del cand[i+1:i+1+need]
            cand_exec, cand_pats, _ = reconstruct_pattern_list(cand, silent=True)
            if not cand_pats or not _pattern_equal(cand_pats[-1], target): break
            s, pattern_list = cand_exec, cand_pats
            if i >= len(s) or s[i] == 0: break
        i = min(i, len(s)-1) - 1
        while i >= 0 and s[i] == 0: i -= 1
    executed, pats, _ = reconstruct_pattern_list(s, silent=True)
    return executed, pats

def _seq_str(nums): return ",".join(str(x) for x in nums)

def parse_o_string(s: str):
    s = s.strip()
    if not s: return Pattern([[]], [set()]), None
    pos, n = 0, len(s)
    rows_desc, steps, masks = [], [], []
    while pos < n:
        if s[pos] != "(": return None, "error"
        pos += 1
        close = s.find(")", pos)
        if close < 0: return None, "error"
        inside = s[pos:close].strip()
        pos = close + 1
        nums, mset = [], set()
        if inside:
            for part in inside.split(","):
                part = part.strip()
                if part.startswith("*"):
                    t = part[1:].strip()
                    if not t.isdigit(): return None, "error"
                    v = int(t); nums.append(v); mset.add(v)
                else:
                    if not part.isdigit(): return None, "error"
                    nums.append(int(part))
        nums = sorted(nums)
        if any(nums[i] == nums[i-1] for i in range(1, len(nums))): return None, "error"
        mset = {x for x in mset if _has(nums, x)}
        if pos >= n or not s[pos].isdigit(): return None, "error"
        j = pos
        while j < n and s[j].isdigit(): j += 1
        steps.append(int(s[pos:j])); pos = j
        rows_desc.append(nums); masks.append(mset)
    return Pattern([steps] + rows_desc, [set()] + masks), None

def _read_find_pattern(I: Pattern):
    C = Pattern(initial_rows, initial_mask)
    ops, pats = [], [C.clone()]
    if compare_patterns(C, I) <= 0: return C, ops, pats
    MAX_OUTER, MAX_N = 50000, 20000
    for _ in range(MAX_OUTER):
        if compare_patterns(C, I) == 0: return C, ops, pats
        n = 0
        while n <= MAX_N:
            Cn, actual = _apply_number(C, n, silent=True)
            if _is_proper_prefix(Cn, I): n += 1; continue
            if compare_patterns(Cn, I) < 0 and not _is_prefix(Cn, I): return C, ops, pats
            if compare_patterns(Cn, I) >= 0:
                if Cn.rows == C.rows and Cn.mask == C.mask: return C, ops, pats
                C = Cn; ops.append(actual); pats.append(C.clone()); break
            n += 1
        else:
            return C, ops, pats
    return C, ops, pats

def main_program():
    op_numbers = []
    op_numbers, pattern_list, _ = reconstruct_pattern_list(op_numbers, silent=True)
    while True:
        cur = pattern_list[-1]
        print("\nCurrent pattern:")
        if cur.is_zero():
            print("(empty)")
        else:
            cur.draw()
        print(f"Operation sequence: {_seq_str(op_numbers)}")
        ptype = "Zero" if cur.is_zero() else ("Successor" if cur.is_succ() else "Limit")
        msg = f"This is a {ptype} pattern. Natural Number: Operation. O: Output. R: Read."
        if len(pattern_list) > 1: msg += " U: Undo."
        msg += " S: Simplify. I: Input operations."
        print(msg)
        user_input = input("Enter your operation: ").strip().upper()

        if user_input.isdigit():
            n_in = int(user_input)
            nxt, actual = _apply_number(cur, n_in, silent=False)
            pattern_list.append(nxt); op_numbers.append(actual)
            print("Applied cut operation." if actual == 0 else f"Applied operation {actual}.")
            continue
        if user_input == "O":
            print(cur.to_string()); continue
        if user_input == "R":
            raw = input("Input pattern string (from O): ").strip()
            pat, err = parse_o_string(raw)
            if err: print("error"); continue
            found, ops, pats = _read_find_pattern(pat)
            op_numbers, pattern_list = ops, pats
            print(found.to_string()); continue
        if user_input == "U" and len(pattern_list) > 1:
            op_numbers = op_numbers[:-1]
            op_numbers, pattern_list, _ = reconstruct_pattern_list(op_numbers, silent=True)
            print("Undo the last operation."); continue
        if user_input == "S":
            new_ops, new_patterns = _simplify(op_numbers, pattern_list)
            if new_ops != op_numbers:
                op_numbers, pattern_list = new_ops, new_patterns
                print(f"Simplified operation sequence: {_seq_str(op_numbers)}")
            else:
                print("No further simplifications possible.")
            continue
        if user_input == "I":
            raw = input("Input the operation sequence (comma-separated natural numbers, e.g., 3,0,2,1): ").strip()
            if not raw: parsed = []
            else:
                parts = [p.strip() for p in raw.split(",")]
                if any((not p.isdigit()) for p in parts): print("error"); continue
                parsed = [int(p) for p in parts]
            op_numbers, pattern_list, _ = reconstruct_pattern_list(parsed, silent=False)
            continue
        print("Invalid operation. Please try again.")

if __name__ == "__main__":
    main_program()

