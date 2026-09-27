"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.Y_FS_variants = Y_FS_variants;
exports.sequence_FS_variants0 = sequence_FS_variants0;
exports.sequence_FS_variants = sequence_FS_variants;
exports.MN_FS_variants = MN_FS_variants;
exports.merge_sum = merge_sum;
exports.FS_default_LNZ_variant = FS_default_LNZ_variant;
function Y_FS_variants(expand_longer, is_infinity, infinity_FS, is_limit, display) {
    const data = {};
    const data_short = {};
    const core = {
        FS: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            const result = core.FS_alter(seq, index);
            return result.slice(0, result.length - 1);
        },
        FS_alter: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            const data_key = display(seq);
            if (data[data_key] === undefined)
                data[data_key] = [];
            else if (data[data_key][index] !== undefined)
                return data[data_key][index];
            return (data[data_key][index] = expand_longer(seq, index));
        },
        FS_short: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            if (index === 0)
                return seq.slice(0, seq.length - 1);
            if (index === 1) {
                const result = core.FS_alter(seq, 1);
                return result.slice(0, seq.length);
            }
            const data_key = display(seq);
            const d = data_short[data_key];
            if (d === undefined) {
                data_short[data_key] = core.FS(seq, 1).length !== seq.length;
            }
            return core.FS(seq, index - (data_short[data_key] ? 1 : 0));
        },
    };
    return core;
}
function sequence_FS_variants0(expand, is_infinity, infinity_FS, is_limit, display) {
    const data = {};
    const data_short = {};
    const core = {
        FS: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            const data_key = display(seq);
            if (data[data_key] === undefined)
                data[data_key] = [];
            else if (data[data_key][index] !== undefined)
                return data[data_key][index];
            return (data[data_key][index] = expand(seq, index));
        },
        FS_short: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            if (index === 0)
                return seq.slice(0, seq.length - 1);
            if (index === 1) {
                const result = core.FS(seq, 1);
                return result.slice(0, seq.length);
            }
            const data_key = display(seq);
            let d = data_short[data_key];
            if (d === undefined) {
                d = data_short[data_key] = core.FS(seq, 0).length !== seq.length;
            }
            return core.FS(seq, index - (d ? 1 : 0));
        },
    };
    return core;
}
function sequence_FS_variants(expand, is_infinity, infinity_FS, is_limit, display) {
    const data = {};
    const data_alter = {};
    const data_short = {};
    const core = {
        FS: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            const data_key = display(seq);
            if (data[data_key] === undefined)
                data[data_key] = [];
            else if (data[data_key][index] !== undefined)
                return data[data_key][index];
            return (data[data_key][index] = expand(seq, index, true));
        },
        FS_alter: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            const data_key = display(seq);
            if (data_alter[data_key] === undefined)
                data_alter[data_key] = [];
            else if (data_alter[data_key][index] !== undefined)
                return data_alter[data_key][index];
            return (data_alter[data_key][index] = expand(seq, index, false));
        },
        FS_short: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            if (index === 0)
                return seq.slice(0, seq.length - 1);
            if (index === 1) {
                const result = core.FS_alter(seq, 1);
                return result.slice(0, seq.length);
            }
            const data_key = display(seq);
            let d = data_short[data_key];
            if (d === undefined) {
                d = data_short[data_key] = core.FS(seq, 1).length !== seq.length;
            }
            return core.FS(seq, index - (d ? 1 : 0));
        },
    };
    return core;
}
function MN_FS_variants(expand, is_infinity, infinity_FS, is_limit, display) {
    const data = {};
    const data_alter = {};
    const data_short = {};
    const core = {
        FS: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            const data_key = display(seq);
            if (data[data_key] === undefined)
                data[data_key] = [];
            else if (data[data_key][index] !== undefined)
                return data[data_key][index];
            return (data[data_key][index] = expand(seq, index, true));
        },
        FS_alter: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            const data_key = display(seq);
            if (data_alter[data_key] === undefined)
                data_alter[data_key] = [];
            else if (data_alter[data_key][index] !== undefined)
                return data_alter[data_key][index];
            return (data_alter[data_key][index] = expand(seq, index, false));
        },
        FS_short: (seq, index) => {
            if (is_infinity(seq))
                return infinity_FS(index);
            if (!seq.length)
                return [];
            if (!is_limit(seq))
                return seq.slice(0, seq.length - 1);
            if (index === 0)
                return seq.slice(0, seq.length - 1);
            const data_key = display(seq);
            let d = data_short[data_key];
            if (d === undefined) {
                let target = core.FS(seq, 1);
                d = data_short[data_key] = [
                    target[seq.length - 1].length !== seq[seq.length - 1].length - 1,
                    target.length !== seq.length,
                ];
            }
            let current = 1;
            if (d[0]) {
                if (index === current) {
                    let result = seq.slice();
                    result[result.length - 1] = result[result.length - 1].slice();
                    result[result.length - 1].pop();
                    return result;
                }
                else
                    current++;
            }
            if (d[1]) {
                if (index === current) {
                    return core.FS(seq, 1).slice(0, seq.length);
                }
                else
                    current++;
            }
            return core.FS(seq, 1 + index - current);
        },
    };
    return core;
}
function merge_sum(terms) {
    let result = [];
    let i = 0;
    while (i < terms.length) {
        let j = i + 1;
        let t = terms[i];
        while (j < terms.length && terms[j] === t)
            j++;
        if (j === i + 1) {
            result.push(terms[i]);
        }
        else {
            let count = j - i;
            if (t === '1')
                result.push('' + count);
            else
                result.push(t + count);
        }
        i = j;
    }
    return result.join('+');
}
function FS_default_LNZ_variant(expand, compare, is_infinity, infinity_FS, is_limit, display) {
    const data = {};
    const data_short = {};
    const data_lnz = {};
    const core = {
        FS: (expr, index) => {
            if (is_infinity(expr))
                return infinity_FS(index);
            if (!is_limit(expr))
                return expand(expr, 0);
            const data_key = display(expr);
            if (data[data_key] === undefined)
                data[data_key] = [];
            else if (data[data_key][index] !== undefined)
                return data[data_key][index];
            return (data[data_key][index] = expand(expr, index));
        },
        FS_short: (expr, index) => {
            if (is_infinity(expr))
                return infinity_FS(index);
            if (!is_limit(expr) || index === 0)
                return expand(expr, 0);
            const data_key = display(expr);
            let d = data_short[data_key];
            if (d === undefined) {
                const truncate = core.FS(expr, 0);
                const FS1 = core.FS(expr, 1);
                let result = FS1;
                while (true) {
                    const result_truncate = core.FS(result, 0);
                    if (compare(result_truncate, truncate) <= 0)
                        break;
                    result = result_truncate;
                }
                d = data_short[data_key] = [compare(result, FS1) !== 0, result];
            }
            if (index === 1)
                return d[1];
            return core.FS(expr, index - (d[0] ? 1 : 0));
        },
    };
    return core;
}
