"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.DisplayMap = exports.DisplaySet = void 0;
exports.number_compare = number_compare;
exports.boolean_compare = boolean_compare;
exports.compare_by = compare_by;
exports.lex_compare = lex_compare;
exports.lex_compare_by = lex_compare_by;
exports.anti_lex_compare = anti_lex_compare;
exports.anti_lex_compare_by = anti_lex_compare_by;
exports.tuple_lex_compare = tuple_lex_compare;
exports.tuple_lex_compare_by = tuple_lex_compare_by;
exports.object_lex_compare = object_lex_compare;
exports.object_lex_compare_by = object_lex_compare_by;
exports.deepcopy = deepcopy;
exports.index_of_first = index_of_first;
exports.index_of_last = index_of_last;
exports.bind1 = bind1;
exports.bind2 = bind2;
exports.bind3 = bind3;
function number_compare(a, b) {
    return a === b ? 0 : a < b ? -1 : 1;
}
function boolean_compare(a, b) {
    return (a ? 1 : 0) - (b ? 1 : 0);
}
function compare_by(transform, cmp) {
    return (a, b) => cmp(transform(a), transform(b));
}
/** 字典序比较（通用）。 */
function lex_compare(a, b, cmp) {
    let len = Math.min(a.length, b.length);
    for (let i = 0; i < len; i++) {
        const result = cmp(a[i], b[i]);
        if (result !== 0)
            return result;
    }
    return number_compare(a.length, b.length);
}
function lex_compare_by(cmp) {
    return (a, b) => lex_compare(a, b, cmp);
}
function anti_lex_compare(a, b, cmp) {
    if (a.length !== b.length)
        return number_compare(a.length, b.length);
    let len = a.length;
    for (let i = len - 1; i >= 0; i--) {
        const result = cmp(a[i], b[i]);
        if (result !== 0)
            return result;
    }
    return 0;
}
function anti_lex_compare_by(cmp) {
    return (a, b) => anti_lex_compare(a, b, cmp);
}
function tuple_lex_compare(a, b, cmp) {
    for (let i = 0; i < cmp.length; i++) {
        const result = cmp[i]?.(a[i], b[i]) ?? 0;
        if (result !== 0)
            return result;
    }
    return 0;
}
function tuple_lex_compare_by(cmp) {
    return (a, b) => tuple_lex_compare(a, b, cmp);
}
function object_lex_compare(a, b, cmp, order) {
    for (let key of order) {
        const result = cmp[key](a[key], b[key]);
        if (result !== 0)
            return result;
    }
    return 0;
}
function object_lex_compare_by(cmp, order) {
    return (a, b) => object_lex_compare(a, b, cmp, order);
}
/** 深度克隆（支持数组和普通对象）。 */
function deepcopy(obj) {
    if (!obj)
        return obj;
    if (typeof obj === 'number' || typeof obj === 'boolean' || typeof obj === 'string')
        return obj;
    if (Array.isArray(obj)) {
        const result = Array.from({ length: obj.length });
        for (let i = 0, len = obj.length; i < len; i++) {
            if (i in obj)
                result[i] = deepcopy(obj[i]);
        }
        return result;
    }
    else {
        const result = {};
        for (const key in obj) {
            result[key] = deepcopy(obj[key]);
        }
        return result;
    }
}
function index_of_first(array, predicate) {
    return array.findIndex(predicate);
}
function index_of_last(array, predicate) {
    for (let i = array.length - 1; i >= 0; i--) {
        if (predicate(array[i]))
            return i;
    }
    return -1;
}
function bind1(fn, t1) {
    return (...t_rest) => fn(t1, ...t_rest);
}
function bind2(fn, t2) {
    return (t1, ...t_rest) => fn(t1, t2, ...t_rest);
}
function bind3(fn, t3) {
    return (t1, t2, ...t_rest) => fn(t1, t2, t3, ...t_rest);
}
/** 以 display 为键的集合，实现值语义去重。 */
class DisplaySet {
    _map;
    _display;
    constructor(display, items) {
        this._display = display;
        this._map = new Map();
        if (items) {
            for (const item of items) {
                this.add(item);
            }
        }
    }
    add(value) {
        this._map.set(this._display(value), value);
        return this;
    }
    has(value) {
        return this._map.has(this._display(value));
    }
    delete(value) {
        return this._map.delete(this._display(value));
    }
    values() {
        return Array.from(this._map.values());
    }
    get size() {
        return this._map.size;
    }
    forEach(callback) {
        this._map.forEach((value) => callback(value));
    }
    [Symbol.iterator]() {
        return this._map.values();
    }
}
exports.DisplaySet = DisplaySet;
/** 以 display 为键的映射，实现值语义键比较。 */
class DisplayMap {
    _map;
    _display;
    constructor(display, entries) {
        this._display = display;
        this._map = new Map();
        if (entries) {
            for (const [key, value] of entries) {
                this.set(key, value);
            }
        }
    }
    set(key, value) {
        this._map.set(this._display(key), [key, value]);
        return this;
    }
    get(key) {
        return this._map.get(this._display(key))?.[1];
    }
    has(key) {
        return this._map.has(this._display(key));
    }
    delete(key) {
        return this._map.delete(this._display(key));
    }
    entries() {
        return Array.from(this._map.values());
    }
    values() {
        return Array.from(this._map.values()).map(([, v]) => v);
    }
    keys() {
        return Array.from(this._map.values()).map(([k]) => k);
    }
    get size() {
        return this._map.size;
    }
    forEach(callback) {
        this._map.forEach(([k, v]) => callback(v, k));
    }
}
exports.DisplayMap = DisplayMap;
