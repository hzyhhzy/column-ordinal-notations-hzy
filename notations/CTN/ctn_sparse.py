"""Sparse finite CTN tables; this does not change the table checker."""

import ctn_table as t


class SparseTable:
    def __init__(self, size, entries):
        self.size, self.entries = size, entries

    def __len__(self):
        return self.size

    def __getitem__(self, index):
        if not 0 <= index < self.size:
            raise IndexError(index)
        return self.entries.get(index, 0)


def metadata(size):
    """Only kinds 0 through 5 can have nonzero values or nontrivial tests.

    All omitted fields are forced to zero and impose no other obligation.
    There are O(sqrt(size)) possibly relevant addresses, not size of them.
    """
    fields = {}
    for kind in range(6):
        data = 0
        while (address := t.pair(kind, data)) < size:
            if kind == t.MEMBERSHIP:
                fields[address] = (kind, data, None)
                data += 1
                continue
            payload, number = t.unpair(data) if kind in (4, 5) else (data, None)
            code, environment = t.unpair(payload)
            nc, sc = t.unpair(environment)
            ns, ss = t.decode_list(nc), t.decode_list(sc)
            extra = int(kind in (3, 4))
            if t.scoped(code, len(ns) + extra, len(ss)):
                fields[address] = (kind, payload, number, code, nc, sc, ns, ss)
            data += 1
    return fields
