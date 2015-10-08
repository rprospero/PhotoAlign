"use strict";
// This object will hold all exports.
var Haste = {};

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof F) {
            f = E(B(f));
        }
        if(f instanceof PAP) {
            // f is a partial application
            if(args.length == f.arity) {
                // Saturated application
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                // Application is still unsaturated
                return new PAP(f.f, f.args.concat(args));
            } else {
                // Application is oversaturated; 
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else if(f instanceof Function) {
            if(args.length == f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        return t.x;
    } else {
        return t;
    }
}

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        f = fun();
    }
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return [0, (a-a%b)/b, a%b];
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return [0, x & 0xffffffff, x > 0x7fffffff];
}

function subC(a, b) {
    var x = a-b;
    return [0, x & 0xffffffff, x < -2147483648];
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, [0]);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return [1,str.charCodeAt(i),new T(function() {
            return unAppCStr(str,chrs,i+1);
        })];
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str[0] == 1; str = E(str[2])) {
        s += String.fromCharCode(E(str[1]));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x[1];
    return x[2];
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Array) {
        return x[0];
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(I_getBits(i,0)) + popCnt(I_getBits(i,1));
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return [0,1,0,0,0];
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return [0, sign*man, exp];
}

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return [0,1,0,0,0];
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return [0, sign, manHigh, manLow, exp];
}

function jsAlert(val) {
    if(typeof alert != 'undefined') {
        alert(val);
    } else {
        print(val);
    }
}

function jsLog(val) {
    console.log(val);
}

function jsPrompt(str) {
    var val;
    if(typeof prompt != 'undefined') {
        val = prompt(str);
    } else {
        print(str);
        val = readline();
    }
    return val == undefined ? '' : val.toString();
}

function jsEval(str) {
    var x = eval(str);
    return x == undefined ? '' : x.toString();
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

function jsGet(elem, prop) {
    return elem[prop].toString();
}

function jsSet(elem, prop, val) {
    elem[prop] = val;
}

function jsGetAttr(elem, prop) {
    if(elem.hasAttribute(prop)) {
        return elem.getAttribute(prop).toString();
    } else {
        return "";
    }
}

function jsSetAttr(elem, prop, val) {
    elem.setAttribute(prop, val);
}

function jsGetStyle(elem, prop) {
    return elem.style[prop].toString();
}

function jsSetStyle(elem, prop, val) {
    elem.style[prop] = val;
}

function jsKillChild(child, parent) {
    parent.removeChild(child);
}

function jsClearChildren(elem) {
    while(elem.hasChildNodes()){
        elem.removeChild(elem.lastChild);
    }
}

function jsFind(elem) {
    var e = document.getElementById(elem)
    if(e) {
        return [1,e];
    }
    return [0];
}

function jsElemsByClassName(cls) {
    var es = document.getElementsByClassName(cls);
    var els = [0];

    for (var i = es.length-1; i >= 0; --i) {
        els = [1, es[i], els];
    }
    return els;
}

function jsQuerySelectorAll(elem, query) {
    var els = [0], nl;

    if (!elem || typeof elem.querySelectorAll !== 'function') {
        return els;
    }

    nl = elem.querySelectorAll(query);

    for (var i = nl.length-1; i >= 0; --i) {
        els = [1, nl[i], els];
    }

    return els;
}

function jsCreateElem(tag) {
    return document.createElement(tag);
}

function jsCreateTextNode(str) {
    return document.createTextNode(str);
}

function jsGetChildBefore(elem) {
    elem = elem.previousSibling;
    while(elem) {
        if(typeof elem.tagName != 'undefined') {
            return [1,elem];
        }
        elem = elem.previousSibling;
    }
    return [0];
}

function jsGetLastChild(elem) {
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,elem.childNodes[i]];
        }
    }
    return [0];
}


function jsGetFirstChild(elem) {
    var len = elem.childNodes.length;
    for(var i = 0; i < len; i++) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,elem.childNodes[i]];
        }
    }
    return [0];
}


function jsGetChildren(elem) {
    var children = [0];
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            children = [1, elem.childNodes[i], children];
        }
    }
    return children;
}

function jsSetChildren(elem, children) {
    children = E(children);
    jsClearChildren(elem, 0);
    while(children[0] === 1) {
        elem.appendChild(E(children[1]));
        children = E(children[2]);
    }
}

function jsAppendChild(child, container) {
    container.appendChild(child);
}

function jsAddChildBefore(child, container, after) {
    container.insertBefore(child, after);
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs[0]) {
        strs = E(strs);
        arr.push(E(strs[1]));
        strs = E(strs[2]);
    }
    return arr.join(sep);
}

// JSON stringify a string
function jsStringify(str) {
    return JSON.stringify(str);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return [0];
    }
    return [1,hs];
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return [0, jsRead(obj)];
    case 'string':
        return [1, obj];
    case 'boolean':
        return [2, obj]; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return [3, arr2lst_json(obj, 0)];
        } else if (obj == null) {
            return [5];
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = [1, [0, ks[i], toHS(obj[ks[i]])], xs];
            }
            return [4, xs];
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, toHS(arr[elem]), new T(function() {return arr2lst_json(arr,elem+1);}),true]
}

function ajaxReq(method, url, async, postdata, cb) {
    var xhr = new XMLHttpRequest();
    xhr.open(method, url, async);

    if(method == "POST") {
        xhr.setRequestHeader("Content-type",
                             "application/x-www-form-urlencoded");
    }
    xhr.onreadystatechange = function() {
        if(xhr.readyState == 4) {
            if(xhr.status == 200) {
                B(A(cb,[[1,xhr.responseText],0]));
            } else {
                B(A(cb,[[0],0])); // Nothing
            }
        }
    }
    xhr.send(postdata);
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

/* Utility functions for working with JSStrings. */

var _jss_singleton = String.fromCharCode;

function _jss_cons(c,s) {return String.fromCharCode(c)+s;}
function _jss_snoc(s,c) {return s+String.fromCharCode(c);}
function _jss_append(a,b) {return a+b;}
function _jss_len(s) {return s.length;}
function _jss_index(s,i) {return s.charCodeAt(i);}
function _jss_drop(s,i) {return s.substr(i);}
function _jss_substr(s,a,b) {return s.substr(a,b);}
function _jss_take(n,s) {return s.substr(0,n);}
// TODO: incorrect for some unusual characters.
function _jss_rev(s) {return s.split("").reverse().join("");}

function _jss_map(f,s) {
    f = E(f);
    var s2 = '';
    for(var i in s) {
        s2 += String.fromCharCode(E(f(s.charCodeAt(i))));
    }
    return s2;
}

function _jss_foldl(f,x,s) {
    f = E(f);
    for(var i in s) {
        x = A(f,[x,s.charCodeAt(i)]);
    }
    return x;
}

function _jss_re_match(s,re) {return s.search(re)>=0;}
function _jss_re_compile(re,fs) {return new RegExp(re,fs);}
function _jss_re_replace(s,re,rep) {return s.replace(re,rep);}

function _jss_re_find(re,s) {
    var a = s.match(re);
    return a ? mklst(a) : [0];
}

function mklst(arr) {
    var l = [0], len = arr.length-1;
    for(var i = 0; i <= len; ++i) {
        l = [1,arr[len-i],l];
    }
    return l;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return [0, 0, undefined];
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return [0, 1, val];
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

var Integer = function(bits, sign) {
  this.bits_ = [];
  this.sign_ = sign;

  var top = true;
  for (var i = bits.length - 1; i >= 0; i--) {
    var val = bits[i] | 0;
    if (!top || val != sign) {
      this.bits_[i] = val;
      top = false;
    }
  }
};

Integer.IntCache_ = {};

var I_fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Integer.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Integer([value | 0], value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Integer.IntCache_[value] = obj;
  }
  return obj;
};

var I_fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Integer.ZERO;
  } else if (value < 0) {
    return I_negate(I_fromNumber(-value));
  } else {
    var bits = [];
    var pow = 1;
    for (var i = 0; value >= pow; i++) {
      bits[i] = (value / pow) | 0;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return new Integer(bits, 0);
  }
};

var I_fromBits = function(bits) {
  var high = bits[bits.length - 1];
  return new Integer(bits, high & (1 << 31) ? -1 : 0);
};

var I_fromString = function(str, opt_radix) {
  if (str.length == 0) {
    throw Error('number format error: empty string');
  }

  var radix = opt_radix || 10;
  if (radix < 2 || 36 < radix) {
    throw Error('radix out of range: ' + radix);
  }

  if (str.charAt(0) == '-') {
    return I_negate(I_fromString(str.substring(1), radix));
  } else if (str.indexOf('-') >= 0) {
    throw Error('number format error: interior "-" character');
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 8));

  var result = Integer.ZERO;
  for (var i = 0; i < str.length; i += 8) {
    var size = Math.min(8, str.length - i);
    var value = parseInt(str.substring(i, i + size), radix);
    if (size < 8) {
      var power = I_fromNumber(Math.pow(radix, size));
      result = I_add(I_mul(result, power), I_fromNumber(value));
    } else {
      result = I_mul(result, radixToPower);
      result = I_add(result, I_fromNumber(value));
    }
  }
  return result;
};


Integer.TWO_PWR_32_DBL_ = (1 << 16) * (1 << 16);
Integer.ZERO = I_fromInt(0);
Integer.ONE = I_fromInt(1);
Integer.TWO_PWR_24_ = I_fromInt(1 << 24);

var I_toInt = function(self) {
  return self.bits_.length > 0 ? self.bits_[0] : self.sign_;
};

var I_toWord = function(self) {
  return I_toInt(self) >>> 0;
};

var I_toNumber = function(self) {
  if (isNegative(self)) {
    return -I_toNumber(I_negate(self));
  } else {
    var val = 0;
    var pow = 1;
    for (var i = 0; i < self.bits_.length; i++) {
      val += I_getBitsUnsigned(self, i) * pow;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return val;
  }
};

var I_getBits = function(self, index) {
  if (index < 0) {
    return 0;
  } else if (index < self.bits_.length) {
    return self.bits_[index];
  } else {
    return self.sign_;
  }
};

var I_getBitsUnsigned = function(self, index) {
  var val = I_getBits(self, index);
  return val >= 0 ? val : Integer.TWO_PWR_32_DBL_ + val;
};

var getSign = function(self) {
  return self.sign_;
};

var isZero = function(self) {
  if (self.sign_ != 0) {
    return false;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    if (self.bits_[i] != 0) {
      return false;
    }
  }
  return true;
};

var isNegative = function(self) {
  return self.sign_ == -1;
};

var isOdd = function(self) {
  return (self.bits_.length == 0) && (self.sign_ == -1) ||
         (self.bits_.length > 0) && ((self.bits_[0] & 1) != 0);
};

var I_equals = function(self, other) {
  if (self.sign_ != other.sign_) {
    return false;
  }
  var len = Math.max(self.bits_.length, other.bits_.length);
  for (var i = 0; i < len; i++) {
    if (I_getBits(self, i) != I_getBits(other, i)) {
      return false;
    }
  }
  return true;
};

var I_notEquals = function(self, other) {
  return !I_equals(self, other);
};

var I_greaterThan = function(self, other) {
  return I_compare(self, other) > 0;
};

var I_greaterThanOrEqual = function(self, other) {
  return I_compare(self, other) >= 0;
};

var I_lessThan = function(self, other) {
  return I_compare(self, other) < 0;
};

var I_lessThanOrEqual = function(self, other) {
  return I_compare(self, other) <= 0;
};

var I_compare = function(self, other) {
  var diff = I_sub(self, other);
  if (isNegative(diff)) {
    return -1;
  } else if (isZero(diff)) {
    return 0;
  } else {
    return +1;
  }
};

var I_compareInt = function(self, other) {
  return I_compare(self, I_fromInt(other));
}

var shorten = function(self, numBits) {
  var arr_index = (numBits - 1) >> 5;
  var bit_index = (numBits - 1) % 32;
  var bits = [];
  for (var i = 0; i < arr_index; i++) {
    bits[i] = I_getBits(self, i);
  }
  var sigBits = bit_index == 31 ? 0xFFFFFFFF : (1 << (bit_index + 1)) - 1;
  var val = I_getBits(self, arr_index) & sigBits;
  if (val & (1 << bit_index)) {
    val |= 0xFFFFFFFF - sigBits;
    bits[arr_index] = val;
    return new Integer(bits, -1);
  } else {
    bits[arr_index] = val;
    return new Integer(bits, 0);
  }
};

var I_negate = function(self) {
  return I_add(not(self), Integer.ONE);
};

var I_add = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  var carry = 0;

  for (var i = 0; i <= len; i++) {
    var a1 = I_getBits(self, i) >>> 16;
    var a0 = I_getBits(self, i) & 0xFFFF;

    var b1 = I_getBits(other, i) >>> 16;
    var b0 = I_getBits(other, i) & 0xFFFF;

    var c0 = carry + a0 + b0;
    var c1 = (c0 >>> 16) + a1 + b1;
    carry = c1 >>> 16;
    c0 &= 0xFFFF;
    c1 &= 0xFFFF;
    arr[i] = (c1 << 16) | c0;
  }
  return I_fromBits(arr);
};

var I_sub = function(self, other) {
  return I_add(self, I_negate(other));
};

var I_mul = function(self, other) {
  if (isZero(self)) {
    return Integer.ZERO;
  } else if (isZero(other)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_mul(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_mul(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_mul(self, I_negate(other)));
  }

  if (I_lessThan(self, Integer.TWO_PWR_24_) &&
      I_lessThan(other, Integer.TWO_PWR_24_)) {
    return I_fromNumber(I_toNumber(self) * I_toNumber(other));
  }

  var len = self.bits_.length + other.bits_.length;
  var arr = [];
  for (var i = 0; i < 2 * len; i++) {
    arr[i] = 0;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    for (var j = 0; j < other.bits_.length; j++) {
      var a1 = I_getBits(self, i) >>> 16;
      var a0 = I_getBits(self, i) & 0xFFFF;

      var b1 = I_getBits(other, j) >>> 16;
      var b0 = I_getBits(other, j) & 0xFFFF;

      arr[2 * i + 2 * j] += a0 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j);
      arr[2 * i + 2 * j + 1] += a1 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 1] += a0 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 2] += a1 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 2);
    }
  }

  for (var i = 0; i < len; i++) {
    arr[i] = (arr[2 * i + 1] << 16) | arr[2 * i];
  }
  for (var i = len; i < 2 * len; i++) {
    arr[i] = 0;
  }
  return new Integer(arr, 0);
};

Integer.carry16_ = function(bits, index) {
  while ((bits[index] & 0xFFFF) != bits[index]) {
    bits[index + 1] += bits[index] >>> 16;
    bits[index] &= 0xFFFF;
  }
};

var I_mod = function(self, other) {
  return I_rem(I_add(other, I_rem(self, other)), other);
}

var I_div = function(self, other) {
  if(I_greaterThan(self, Integer.ZERO) != I_greaterThan(other, Integer.ZERO)) {
    if(I_rem(self, other) != Integer.ZERO) {
      return I_sub(I_quot(self, other), Integer.ONE);
    }
  }
  return I_quot(self, other);
}

var I_quotRem = function(self, other) {
  return [0, I_quot(self, other), I_rem(self, other)];
}

var I_divMod = function(self, other) {
  return [0, I_div(self, other), I_mod(self, other)];
}

var I_quot = function(self, other) {
  if (isZero(other)) {
    throw Error('division by zero');
  } else if (isZero(self)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_quot(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_quot(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_quot(self, I_negate(other)));
  }

  var res = Integer.ZERO;
  var rem = self;
  while (I_greaterThanOrEqual(rem, other)) {
    var approx = Math.max(1, Math.floor(I_toNumber(rem) / I_toNumber(other)));
    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);
    var approxRes = I_fromNumber(approx);
    var approxRem = I_mul(approxRes, other);
    while (isNegative(approxRem) || I_greaterThan(approxRem, rem)) {
      approx -= delta;
      approxRes = I_fromNumber(approx);
      approxRem = I_mul(approxRes, other);
    }

    if (isZero(approxRes)) {
      approxRes = Integer.ONE;
    }

    res = I_add(res, approxRes);
    rem = I_sub(rem, approxRem);
  }
  return res;
};

var I_rem = function(self, other) {
  return I_sub(self, I_mul(I_quot(self, other), other));
};

var not = function(self) {
  var len = self.bits_.length;
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = ~self.bits_[i];
  }
  return new Integer(arr, ~self.sign_);
};

var I_and = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) & I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ & other.sign_);
};

var I_or = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) | I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ | other.sign_);
};

var I_xor = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) ^ I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ ^ other.sign_);
};

var I_shiftLeft = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length + arr_delta + (bit_delta > 0 ? 1 : 0);
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i - arr_delta) << bit_delta) |
               (I_getBits(self, i - arr_delta - 1) >>> (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i - arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_shiftRight = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length - arr_delta;
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i + arr_delta) >>> bit_delta) |
               (I_getBits(self, i + arr_delta + 1) << (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i + arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_signum = function(self) {
  var cmp = I_compare(self, Integer.ZERO);
  if(cmp > 0) {
    return Integer.ONE
  }
  if(cmp < 0) {
    return I_sub(Integer.ZERO, Integer.ONE);
  }
  return Integer.ZERO;
};

var I_abs = function(self) {
  if(I_compare(self, Integer.ZERO) < 0) {
    return I_sub(Integer.ZERO, self);
  }
  return self;
};

var I_decodeDouble = function(x) {
  var dec = decodeDouble(x);
  var mantissa = I_fromBits([dec[3], dec[2]]);
  if(dec[1] < 0) {
    mantissa = I_negate(mantissa);
  }
  return [0, dec[4], mantissa];
}

var I_toString = function(self) {
  var radix = 10;

  if (isZero(self)) {
    return '0';
  } else if (isNegative(self)) {
    return '-' + I_toString(I_negate(self));
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 6));

  var rem = self;
  var result = '';
  while (true) {
    var remDiv = I_div(rem, radixToPower);
    var intval = I_toInt(I_sub(rem, I_mul(remDiv, radixToPower)));
    var digits = intval.toString();

    rem = remDiv;
    if (isZero(rem)) {
      return digits + result;
    } else {
      while (digits.length < 6) {
        digits = '0' + digits;
      }
      result = '' + digits + result;
    }
  }
};

var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    return I_fromBits([x.getLowBits(), x.getHighBits()]);
}

function I_toInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

function I_fromWord64(x) {
    return x;
}

function I_toWord64(x) {
    return I_rem(I_add(__w64_max, x), __w64_max);
}

// Copyright 2009 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

var Long = function(low, high) {
  this.low_ = low | 0;
  this.high_ = high | 0;
};

Long.IntCache_ = {};

Long.fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Long.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Long(value | 0, value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Long.IntCache_[value] = obj;
  }
  return obj;
};

Long.fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Long.ZERO;
  } else if (value <= -Long.TWO_PWR_63_DBL_) {
    return Long.MIN_VALUE;
  } else if (value + 1 >= Long.TWO_PWR_63_DBL_) {
    return Long.MAX_VALUE;
  } else if (value < 0) {
    return Long.fromNumber(-value).negate();
  } else {
    return new Long(
        (value % Long.TWO_PWR_32_DBL_) | 0,
        (value / Long.TWO_PWR_32_DBL_) | 0);
  }
};

Long.fromBits = function(lowBits, highBits) {
  return new Long(lowBits, highBits);
};

Long.TWO_PWR_16_DBL_ = 1 << 16;
Long.TWO_PWR_24_DBL_ = 1 << 24;
Long.TWO_PWR_32_DBL_ =
    Long.TWO_PWR_16_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_31_DBL_ =
    Long.TWO_PWR_32_DBL_ / 2;
Long.TWO_PWR_48_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_64_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_32_DBL_;
Long.TWO_PWR_63_DBL_ =
    Long.TWO_PWR_64_DBL_ / 2;
Long.ZERO = Long.fromInt(0);
Long.ONE = Long.fromInt(1);
Long.NEG_ONE = Long.fromInt(-1);
Long.MAX_VALUE =
    Long.fromBits(0xFFFFFFFF | 0, 0x7FFFFFFF | 0);
Long.MIN_VALUE = Long.fromBits(0, 0x80000000 | 0);
Long.TWO_PWR_24_ = Long.fromInt(1 << 24);

Long.prototype.toInt = function() {
  return this.low_;
};

Long.prototype.toNumber = function() {
  return this.high_ * Long.TWO_PWR_32_DBL_ +
         this.getLowBitsUnsigned();
};

Long.prototype.getHighBits = function() {
  return this.high_;
};

Long.prototype.getLowBits = function() {
  return this.low_;
};

Long.prototype.getLowBitsUnsigned = function() {
  return (this.low_ >= 0) ?
      this.low_ : Long.TWO_PWR_32_DBL_ + this.low_;
};

Long.prototype.isZero = function() {
  return this.high_ == 0 && this.low_ == 0;
};

Long.prototype.isNegative = function() {
  return this.high_ < 0;
};

Long.prototype.isOdd = function() {
  return (this.low_ & 1) == 1;
};

Long.prototype.equals = function(other) {
  return (this.high_ == other.high_) && (this.low_ == other.low_);
};

Long.prototype.notEquals = function(other) {
  return (this.high_ != other.high_) || (this.low_ != other.low_);
};

Long.prototype.lessThan = function(other) {
  return this.compare(other) < 0;
};

Long.prototype.lessThanOrEqual = function(other) {
  return this.compare(other) <= 0;
};

Long.prototype.greaterThan = function(other) {
  return this.compare(other) > 0;
};

Long.prototype.greaterThanOrEqual = function(other) {
  return this.compare(other) >= 0;
};

Long.prototype.compare = function(other) {
  if (this.equals(other)) {
    return 0;
  }

  var thisNeg = this.isNegative();
  var otherNeg = other.isNegative();
  if (thisNeg && !otherNeg) {
    return -1;
  }
  if (!thisNeg && otherNeg) {
    return 1;
  }

  if (this.subtract(other).isNegative()) {
    return -1;
  } else {
    return 1;
  }
};

Long.prototype.negate = function() {
  if (this.equals(Long.MIN_VALUE)) {
    return Long.MIN_VALUE;
  } else {
    return this.not().add(Long.ONE);
  }
};

Long.prototype.add = function(other) {
  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 + b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 + b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 + b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 + b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.subtract = function(other) {
  return this.add(other.negate());
};

Long.prototype.multiply = function(other) {
  if (this.isZero()) {
    return Long.ZERO;
  } else if (other.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    return other.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  } else if (other.equals(Long.MIN_VALUE)) {
    return this.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().multiply(other.negate());
    } else {
      return this.negate().multiply(other).negate();
    }
  } else if (other.isNegative()) {
    return this.multiply(other.negate()).negate();
  }

  if (this.lessThan(Long.TWO_PWR_24_) &&
      other.lessThan(Long.TWO_PWR_24_)) {
    return Long.fromNumber(this.toNumber() * other.toNumber());
  }

  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 * b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 * b00;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c16 += a00 * b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 * b00;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a16 * b16;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a00 * b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.div = function(other) {
  if (other.isZero()) {
    throw Error('division by zero');
  } else if (this.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    if (other.equals(Long.ONE) ||
        other.equals(Long.NEG_ONE)) {
      return Long.MIN_VALUE;
    } else if (other.equals(Long.MIN_VALUE)) {
      return Long.ONE;
    } else {
      var halfThis = this.shiftRight(1);
      var approx = halfThis.div(other).shiftLeft(1);
      if (approx.equals(Long.ZERO)) {
        return other.isNegative() ? Long.ONE : Long.NEG_ONE;
      } else {
        var rem = this.subtract(other.multiply(approx));
        var result = approx.add(rem.div(other));
        return result;
      }
    }
  } else if (other.equals(Long.MIN_VALUE)) {
    return Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().div(other.negate());
    } else {
      return this.negate().div(other).negate();
    }
  } else if (other.isNegative()) {
    return this.div(other.negate()).negate();
  }

  var res = Long.ZERO;
  var rem = this;
  while (rem.greaterThanOrEqual(other)) {
    var approx = Math.max(1, Math.floor(rem.toNumber() / other.toNumber()));

    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);

    var approxRes = Long.fromNumber(approx);
    var approxRem = approxRes.multiply(other);
    while (approxRem.isNegative() || approxRem.greaterThan(rem)) {
      approx -= delta;
      approxRes = Long.fromNumber(approx);
      approxRem = approxRes.multiply(other);
    }

    if (approxRes.isZero()) {
      approxRes = Long.ONE;
    }

    res = res.add(approxRes);
    rem = rem.subtract(approxRem);
  }
  return res;
};

Long.prototype.modulo = function(other) {
  return this.subtract(this.div(other).multiply(other));
};

Long.prototype.not = function() {
  return Long.fromBits(~this.low_, ~this.high_);
};

Long.prototype.and = function(other) {
  return Long.fromBits(this.low_ & other.low_,
                                 this.high_ & other.high_);
};

Long.prototype.or = function(other) {
  return Long.fromBits(this.low_ | other.low_,
                                 this.high_ | other.high_);
};

Long.prototype.xor = function(other) {
  return Long.fromBits(this.low_ ^ other.low_,
                                 this.high_ ^ other.high_);
};

Long.prototype.shiftLeft = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var low = this.low_;
    if (numBits < 32) {
      var high = this.high_;
      return Long.fromBits(
          low << numBits,
          (high << numBits) | (low >>> (32 - numBits)));
    } else {
      return Long.fromBits(0, low << (numBits - 32));
    }
  }
};

Long.prototype.shiftRight = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >> numBits);
    } else {
      return Long.fromBits(
          high >> (numBits - 32),
          high >= 0 ? 0 : -1);
    }
  }
};

Long.prototype.shiftRightUnsigned = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >>> numBits);
    } else if (numBits == 32) {
      return Long.fromBits(high, 0);
    } else {
      return Long.fromBits(high >>> (numBits - 32), 0);
    }
  }
};



// Int64
function hs_eqInt64(x, y) {return x.equals(y);}
function hs_neInt64(x, y) {return !x.equals(y);}
function hs_ltInt64(x, y) {return x.compare(y) < 0;}
function hs_leInt64(x, y) {return x.compare(y) <= 0;}
function hs_gtInt64(x, y) {return x.compare(y) > 0;}
function hs_geInt64(x, y) {return x.compare(y) >= 0;}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shiftLeft(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shiftRight(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shiftRightUnsigned(bits);}
function hs_intToInt64(x) {return new Long(x, 0);}
function hs_int64ToInt(x) {return x.toInt();}



// Word64
function hs_wordToWord64(x) {
    return I_fromInt(x);
}
function hs_word64ToWord(x) {
    return I_toInt(x);
}
function hs_mkWord64(low, high) {
    return I_fromBits([low, high]);
}

var hs_and64 = I_and;
var hs_or64 = I_or;
var hs_xor64 = I_xor;
var __i64_all_ones = I_fromBits([0xffffffff, 0xffffffff]);
function hs_not64(x) {
    return I_xor(x, __i64_all_ones);
}
var hs_eqWord64 = I_equals;
var hs_neWord64 = I_notEquals;
var hs_ltWord64 = I_lessThan;
var hs_leWord64 = I_lessThanOrEqual;
var hs_gtWord64 = I_greaterThan;
var hs_geWord64 = I_greaterThanOrEqual;
var hs_quotWord64 = I_quot;
var hs_remWord64 = I_rem;
var __w64_max = I_fromBits([0,0,1]);
function hs_uncheckedShiftL64(x, bits) {
    return I_rem(I_shiftLeft(x, bits), __w64_max);
}
var hs_uncheckedShiftRL64 = I_shiftRight;
function hs_int64ToWord64(x) {
    var tmp = I_add(__w64_max, I_fromBits([x.getLowBits(), x.getHighBits()]));
    return I_rem(tmp, __w64_max);
}
function hs_word64ToInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}
window['newByteArr'] = newByteArr;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// 2D Canvas drawing primitives.
function jsHasCtx2D(elem) {return !!elem.getContext;}
function jsGetCtx2D(elem) {return elem.getContext('2d');}
function jsBeginPath(ctx) {ctx.beginPath();}
function jsMoveTo(ctx, x, y) {ctx.moveTo(x, y);}
function jsLineTo(ctx, x, y) {ctx.lineTo(x, y);}
function jsStroke(ctx) {ctx.stroke();}
function jsFill(ctx) {ctx.fill();}
function jsRotate(ctx, radians) {ctx.rotate(radians);}
function jsTranslate(ctx, x, y) {ctx.translate(x, y);}
function jsScale(ctx, x, y) {ctx.scale(x, y);}
function jsPushState(ctx) {ctx.save();}
function jsPopState(ctx) {ctx.restore();}
function jsResetCanvas(el) {el.width = el.width;}
function jsDrawImage(ctx, img, x, y) {ctx.drawImage(img, x, y);}
function jsDrawImageClipped(ctx, img, x, y, cx, cy, cw, ch) {
    ctx.drawImage(img, cx, cy, cw, ch, x, y, cw, ch);
}
function jsDrawText(ctx, str, x, y) {ctx.fillText(str, x, y);}
function jsClip(ctx) {ctx.clip();}
function jsArc(ctx, x, y, radius, fromAngle, toAngle) {
    ctx.arc(x, y, radius, fromAngle, toAngle);
}
function jsCanvasToDataURL(el) {return el.toDataURL('image/png');}

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return [0, 1, E(w).val];
}

function finalizeWeak(w) {
    return [0, B(A(E(w).fin, [0]))];
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as[0] === 1; as = as[2]) {
        arr.push(as[1]);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, arr[elem],new T(function(){return __arr2lst(elem+1,arr);})]
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs[0] === 1; xs = E(xs[2])) {
        arr.push(E(xs[1]));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0="src",_1=function(_2){return E(E(_2)[2]);},_3=function(_4,_5){var _6=function(_){var _7=jsCreateElem("img"),_8=jsSet(_7,E(_0),toJSStr(E(_5)));return _7;};return new F(function(){return A(_1,[_4,_6]);});},_9=0,_a=function(_){return _9;},_b=function(_c,_d,_){return new F(function(){return _a(_);});},_e="scroll",_f="submit",_g="blur",_h="focus",_i="change",_j="unload",_k="load",_l=function(_m){switch(E(_m)){case 0:return E(_k);case 1:return E(_j);case 2:return E(_i);case 3:return E(_h);case 4:return E(_g);case 5:return E(_f);default:return E(_e);}},_n=[0,_l,_b],_o=function(_p,_){return [1,_p];},_q=function(_r){return E(_r);},_s=[0,_q,_o],_t=function(_u){return E(E(_u)[1]);},_v=function(_w,_x){return (!B(A(_t,[_y,_w,_x])))?true:false;},_z=function(_A,_B){var _C=strEq(E(_A),E(_B));return (E(_C)==0)?false:true;},_D=function(_E,_F){return new F(function(){return _z(_E,_F);});},_y=new T(function(){return [0,_D,_v];}),_G=function(_H,_I){var _J=E(_H);if(!_J[0]){return E(_I);}else{var _K=_J[2],_L=new T(function(){return B(_G(_K,_I));});return [1,_J[1],_L];}},_M=new T(function(){return B(unCStr("!!: negative index"));}),_N=new T(function(){return B(unCStr("Prelude."));}),_O=new T(function(){return B(_G(_N,_M));}),_P=new T(function(){return B(err(_O));}),_Q=new T(function(){return B(unCStr("!!: index too large"));}),_R=new T(function(){return B(_G(_N,_Q));}),_S=new T(function(){return B(err(_R));}),_T=function(_U,_V){while(1){var _W=E(_U);if(!_W[0]){return E(_S);}else{var _X=E(_V);if(!_X){return E(_W[1]);}else{_U=_W[2];_V=_X-1|0;continue;}}}},_Y=function(_Z,_10){if(_10>=0){return new F(function(){return _T(_Z,_10);});}else{return E(_P);}},_11=new T(function(){return B(unCStr(": empty list"));}),_12=function(_13){var _14=new T(function(){return B(_G(_13,_11));},1);return new F(function(){return err(B(_G(_N,_14)));});},_15=new T(function(){return B(unCStr("head"));}),_16=new T(function(){return B(_12(_15));}),_17=function(_18){var _19=E(_18);if(_19[0]==3){var _1a=E(_19[1]);if(!_1a[0]){return E(_16);}else{var _1b=E(_1a[1]);if(!_1b[0]){var _1c=B(_Y(_1a,1));return (_1c[0]==0)?[1,[0,_1b[1],_1c[1]]]:[0];}else{return [0];}}}else{return [0];}},_1d=function(_1e,_1f){var _1g=E(_1f);if(!_1g[0]){return [0];}else{var _1h=_1g[1],_1i=_1g[2],_1j=new T(function(){return B(_1d(_1e,_1i));}),_1k=new T(function(){return B(A(_1e,[_1h]));});return [1,_1k,_1j];}},_1l=function(_1m){var _1n=E(_1m);if(_1n[0]==3){var _1o=B(_1d(_17,_1n[1]));if(!_1o[0]){return E(_16);}else{var _1p=E(_1o[1]);if(!_1p[0]){return [0];}else{var _1q=B(_Y(_1o,1));if(!_1q[0]){return [0];}else{var _1r=B(_Y(_1o,2));if(!_1r[0]){return [0];}else{var _1s=B(_Y(_1o,3));return (_1s[0]==0)?[0]:[1,[0,_1p[1],_1q[1],_1r[1],_1s[1]]];}}}}}else{return [0];}},_1t="box",_1u="mouse",_1v="corner",_1w="Dragging",_1x=[0],_1y=[1,_1x],_1z="Free",_1A="state",_1B=1,_1C=[1,_1B],_1D=0,_1E=[1,_1D],_1F=3,_1G=[1,_1F],_1H=2,_1I=[1,_1H],_1J=new T(function(){return B(unCStr("SW"));}),_1K=new T(function(){return B(unCStr("SE"));}),_1L=new T(function(){return B(unCStr("NW"));}),_1M=new T(function(){return B(unCStr("NE"));}),_1N=function(_1O,_1P){while(1){var _1Q=E(_1O);if(!_1Q[0]){return (E(_1P)[0]==0)?true:false;}else{var _1R=E(_1P);if(!_1R[0]){return false;}else{if(E(_1Q[1])!=E(_1R[1])){return false;}else{_1O=_1Q[2];_1P=_1R[2];continue;}}}}},_1S=function(_1T){var _1U=E(_1T);if(_1U[0]==1){var _1V=fromJSStr(_1U[1]);return (!B(_1N(_1V,_1M)))?(!B(_1N(_1V,_1L)))?(!B(_1N(_1V,_1K)))?(!B(_1N(_1V,_1J)))?[0]:E(_1I):E(_1G):E(_1E):E(_1C);}else{return [0];}},_1W=function(_1X,_1Y,_1Z){while(1){var _20=E(_1Z);if(!_20[0]){return [0];}else{var _21=E(_20[1]);if(!B(A(_t,[_1X,_1Y,_21[1]]))){_1Z=_20[2];continue;}else{return [1,_21[2]];}}}},_22=function(_23){var _24=E(_23);if(_24[0]==4){var _25=_24[1],_26=B(_1W(_y,_1A,_25));if(!_26[0]){return [0];}else{var _27=E(_26[1]);if(_27[0]==1){var _28=_27[1],_29=strEq(_28,E(_1z));if(!E(_29)){var _2a=strEq(_28,E(_1w));if(!E(_2a)){return [0];}else{var _2b=B(_1W(_y,_1v,_25));if(!_2b[0]){return [0];}else{var _2c=B(_1S(_2b[1]));return (_2c[0]==0)?[0]:[1,[1,_2c[1]]];}}}else{return E(_1y);}}else{return [0];}}}else{return [0];}},_2d=function(_2e){var _2f=E(_2e);if(_2f[0]==4){var _2g=_2f[1],_2h=B(_1W(_y,_1u,_2g));if(!_2h[0]){return [0];}else{var _2i=B(_22(_2h[1]));if(!_2i[0]){return [0];}else{var _2j=B(_1W(_y,_1t,_2g));if(!_2j[0]){return [0];}else{var _2k=B(_1l(_2j[1]));return (_2k[0]==0)?[0]:[1,[0,_2i[1],_2k[1]]];}}}}else{return [0];}},_2l=function(_2m){return [0,E(_2m)];},_2n=function(_2o){var _2p=E(_2o);return (_2p[0]==0)?[1,_2p[1]]:[0];},_2q=[0,_2l,_2n],_2r=1,_2s=[1,_2r],_2t=0,_2u=[1,_2t],_2v=new T(function(){return B(unCStr("Free"));}),_2w=new T(function(){return B(unCStr("Dragging"));}),_2x=function(_2y){var _2z=E(_2y);if(_2z[0]==1){var _2A=fromJSStr(_2z[1]);return (!B(_1N(_2A,_2w)))?(!B(_1N(_2A,_2v)))?[0]:E(_2u):E(_2s);}else{return [0];}},_2B="title",_2C="points",_2D=function(_2E){var _2F=E(_2E);if(_2F[0]==4){var _2G=_2F[1],_2H=B(_1W(_y,_2C,_2G));if(!_2H[0]){return [0];}else{var _2I=E(_2H[1]);if(_2I[0]==3){var _2J=E(_2I[1]);if(!_2J[0]){return E(_16);}else{var _2K=E(_2J[1]);if(_2K[0]==3){var _2L=E(_2K[1]);if(!_2L[0]){return E(_16);}else{var _2M=E(_2L[1]);if(!_2M[0]){var _2N=B(_Y(_2L,1));if(!_2N[0]){var _2O=B(_Y(_2J,1));if(_2O[0]==3){var _2P=E(_2O[1]);if(!_2P[0]){return E(_16);}else{var _2Q=E(_2P[1]);if(!_2Q[0]){var _2R=B(_Y(_2P,1));if(!_2R[0]){var _2S=B(_1W(_y,_2B,_2G));if(!_2S[0]){return [0];}else{var _2T=E(_2S[1]);if(_2T[0]==1){var _2U=_2T[1],_2V=new T(function(){return fromJSStr(_2U);});return [1,[0,[0,_2M[1],_2N[1]],[0,_2Q[1],_2R[1]],_2V]];}else{return [0];}}}else{return [0];}}else{return [0];}}}else{return [0];}}else{return [0];}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}},_2W=[0],_2X=function(_2Y){var _2Z=new T(function(){var _30=E(E(_2Y)[2]),_31=_30[1],_32=_30[2],_33=new T(function(){return B(_2l(_32));}),_34=new T(function(){return B(_2l(_31));});return [3,[1,_34,[1,_33,_2W]]];}),_35=new T(function(){var _36=E(E(_2Y)[1]),_37=_36[1],_38=_36[2],_39=new T(function(){return B(_2l(_38));}),_3a=new T(function(){return B(_2l(_37));});return [3,[1,_3a,[1,_39,_2W]]];}),_3b=new T(function(){return [1,toJSStr(E(E(_2Y)[3]))];});return [1,[0,_2B,_3b],[1,[0,_2C,[3,[1,_35,[1,_2Z,_2W]]]],_2W]];},_3c=function(_3d){return [4,E(B(_2X(_3d)))];},_3e=[0,_3c,_2D],_3f="rotations",_3g="fileName",_3h="scans",_3i="mouse",_3j=[1,_2W],_3k=function(_3l){return E(E(_3l)[2]);},_3m=function(_3n,_3o){var _3p=E(_3o);if(_3p[0]==3){var _3q=new T(function(){return B(_3k(_3n));}),_3r=function(_3s){var _3t=E(_3s);if(!_3t[0]){return E(_3j);}else{var _3u=B(A(_3q,[_3t[1]]));if(!_3u[0]){return [0];}else{var _3v=B(_3r(_3t[2]));return (_3v[0]==0)?[0]:[1,[1,_3u[1],_3v[1]]];}}};return new F(function(){return _3r(_3p[1]);});}else{return [0];}},_3w=function(_3x){var _3y=E(_3x);if(_3y[0]==4){var _3z=_3y[1],_3A=B(_1W(_y,_3i,_3z));if(!_3A[0]){return [0];}else{var _3B=B(_2x(_3A[1]));if(!_3B[0]){return [0];}else{var _3C=B(_1W(_y,_3h,_3z));if(!_3C[0]){return [0];}else{var _3D=B(_3m(_3e,_3C[1]));if(!_3D[0]){return [0];}else{var _3E=B(_1W(_y,_3g,_3z));if(!_3E[0]){return [0];}else{var _3F=E(_3E[1]);if(_3F[0]==1){var _3G=_3F[1],_3H=B(_1W(_y,_3f,_3z));if(!_3H[0]){return [0];}else{var _3I=B(_3m(_2q,_3H[1]));if(!_3I[0]){return [0];}else{var _3J=new T(function(){return fromJSStr(_3G);});return [1,[0,_3B[1],_3D[1],_3J,_3I[1]]];}}}else{return [0];}}}}}}}else{return [0];}},_3K="scans",_3L="calib",_3M=function(_3N){var _3O=E(_3N);if(_3O[0]==4){var _3P=_3O[1],_3Q=B(_1W(_y,_3L,_3P));if(!_3Q[0]){return [0];}else{var _3R=B(_2d(_3Q[1]));if(!_3R[0]){return [0];}else{var _3S=B(_1W(_y,_3K,_3P));if(!_3S[0]){return [0];}else{var _3T=B(_3w(_3S[1]));return (_3T[0]==0)?[0]:[1,[0,_3R[1],_3T[1]]];}}}}else{return [0];}},_3U=function(_3V,_3W,_){var _3X=B(A(_3V,[_])),_3Y=B(A(_3W,[_]));return _3X;},_3Z=function(_40,_41,_){var _42=B(A(_40,[_])),_43=_42,_44=B(A(_41,[_])),_45=_44;return new T(function(){return B(A(_43,[_45]));});},_46=function(_47,_48,_){var _49=B(A(_48,[_]));return _47;},_4a=function(_4b,_4c,_){var _4d=B(A(_4c,[_])),_4e=_4d;return new T(function(){return B(A(_4b,[_4e]));});},_4f=[0,_4a,_46],_4g=function(_4h,_){return _4h;},_4i=function(_4j,_4k,_){var _4l=B(A(_4j,[_]));return new F(function(){return A(_4k,[_]);});},_4m=[0,_4f,_4g,_3Z,_4i,_3U],_4n=function(_4o,_4p,_){var _4q=B(A(_4o,[_]));return new F(function(){return A(_4p,[_4q,_]);});},_4r=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_4s=new T(function(){return B(unCStr("base"));}),_4t=new T(function(){return B(unCStr("IOException"));}),_4u=new T(function(){var _4v=hs_wordToWord64(4053623282),_4w=hs_wordToWord64(3693590983);return [0,_4v,_4w,[0,_4v,_4w,_4s,_4r,_4t],_2W,_2W];}),_4x=function(_4y){return E(_4u);},_4z=function(_4A){return E(E(_4A)[1]);},_4B=function(_4C,_4D,_4E){var _4F=B(A(_4C,[_])),_4G=B(A(_4D,[_])),_4H=hs_eqWord64(_4F[1],_4G[1]);if(!_4H){return [0];}else{var _4I=hs_eqWord64(_4F[2],_4G[2]);return (!_4I)?[0]:[1,_4E];}},_4J=function(_4K){var _4L=E(_4K);return new F(function(){return _4B(B(_4z(_4L[1])),_4x,_4L[2]);});},_4M=new T(function(){return B(unCStr(": "));}),_4N=new T(function(){return B(unCStr(")"));}),_4O=new T(function(){return B(unCStr(" ("));}),_4P=new T(function(){return B(unCStr("interrupted"));}),_4Q=new T(function(){return B(unCStr("system error"));}),_4R=new T(function(){return B(unCStr("unsatisified constraints"));}),_4S=new T(function(){return B(unCStr("user error"));}),_4T=new T(function(){return B(unCStr("permission denied"));}),_4U=new T(function(){return B(unCStr("illegal operation"));}),_4V=new T(function(){return B(unCStr("end of file"));}),_4W=new T(function(){return B(unCStr("resource exhausted"));}),_4X=new T(function(){return B(unCStr("resource busy"));}),_4Y=new T(function(){return B(unCStr("does not exist"));}),_4Z=new T(function(){return B(unCStr("already exists"));}),_50=new T(function(){return B(unCStr("resource vanished"));}),_51=new T(function(){return B(unCStr("timeout"));}),_52=new T(function(){return B(unCStr("unsupported operation"));}),_53=new T(function(){return B(unCStr("hardware fault"));}),_54=new T(function(){return B(unCStr("inappropriate type"));}),_55=new T(function(){return B(unCStr("invalid argument"));}),_56=new T(function(){return B(unCStr("failed"));}),_57=new T(function(){return B(unCStr("protocol error"));}),_58=function(_59,_5a){switch(E(_59)){case 0:return new F(function(){return _G(_4Z,_5a);});break;case 1:return new F(function(){return _G(_4Y,_5a);});break;case 2:return new F(function(){return _G(_4X,_5a);});break;case 3:return new F(function(){return _G(_4W,_5a);});break;case 4:return new F(function(){return _G(_4V,_5a);});break;case 5:return new F(function(){return _G(_4U,_5a);});break;case 6:return new F(function(){return _G(_4T,_5a);});break;case 7:return new F(function(){return _G(_4S,_5a);});break;case 8:return new F(function(){return _G(_4R,_5a);});break;case 9:return new F(function(){return _G(_4Q,_5a);});break;case 10:return new F(function(){return _G(_57,_5a);});break;case 11:return new F(function(){return _G(_56,_5a);});break;case 12:return new F(function(){return _G(_55,_5a);});break;case 13:return new F(function(){return _G(_54,_5a);});break;case 14:return new F(function(){return _G(_53,_5a);});break;case 15:return new F(function(){return _G(_52,_5a);});break;case 16:return new F(function(){return _G(_51,_5a);});break;case 17:return new F(function(){return _G(_50,_5a);});break;default:return new F(function(){return _G(_4P,_5a);});}},_5b=new T(function(){return B(unCStr("}"));}),_5c=new T(function(){return B(unCStr("{handle: "));}),_5d=function(_5e,_5f,_5g,_5h,_5i,_5j){var _5k=new T(function(){var _5l=new T(function(){var _5m=new T(function(){var _5n=E(_5h);if(!_5n[0]){return E(_5j);}else{var _5o=new T(function(){var _5p=new T(function(){return B(_G(_4N,_5j));},1);return B(_G(_5n,_5p));},1);return B(_G(_4O,_5o));}},1);return B(_58(_5f,_5m));}),_5q=E(_5g);if(!_5q[0]){return E(_5l);}else{var _5r=new T(function(){return B(_G(_4M,_5l));},1);return B(_G(_5q,_5r));}}),_5s=E(_5i);if(!_5s[0]){var _5t=E(_5e);if(!_5t[0]){return E(_5k);}else{var _5u=E(_5t[1]);if(!_5u[0]){var _5v=_5u[1],_5w=new T(function(){var _5x=new T(function(){var _5y=new T(function(){return B(_G(_4M,_5k));},1);return B(_G(_5b,_5y));},1);return B(_G(_5v,_5x));},1);return new F(function(){return _G(_5c,_5w);});}else{var _5z=_5u[1],_5A=new T(function(){var _5B=new T(function(){var _5C=new T(function(){return B(_G(_4M,_5k));},1);return B(_G(_5b,_5C));},1);return B(_G(_5z,_5B));},1);return new F(function(){return _G(_5c,_5A);});}}}else{var _5D=new T(function(){return B(_G(_4M,_5k));},1);return new F(function(){return _G(_5s[1],_5D);});}},_5E=function(_5F){var _5G=E(_5F);return new F(function(){return _5d(_5G[1],_5G[2],_5G[3],_5G[4],_5G[6],_2W);});},_5H=function(_5I,_5J,_5K){var _5L=E(_5J);return new F(function(){return _5d(_5L[1],_5L[2],_5L[3],_5L[4],_5L[6],_5K);});},_5M=function(_5N,_5O){var _5P=E(_5N);return new F(function(){return _5d(_5P[1],_5P[2],_5P[3],_5P[4],_5P[6],_5O);});},_5Q=44,_5R=93,_5S=91,_5T=function(_5U,_5V,_5W){var _5X=E(_5V);if(!_5X[0]){return new F(function(){return unAppCStr("[]",_5W);});}else{var _5Y=_5X[1],_5Z=_5X[2],_60=new T(function(){var _61=new T(function(){var _62=[1,_5R,_5W],_63=function(_64){var _65=E(_64);if(!_65[0]){return E(_62);}else{var _66=_65[1],_67=_65[2],_68=new T(function(){var _69=new T(function(){return B(_63(_67));});return B(A(_5U,[_66,_69]));});return [1,_5Q,_68];}};return B(_63(_5Z));});return B(A(_5U,[_5Y,_61]));});return [1,_5S,_60];}},_6a=function(_6b,_6c){return new F(function(){return _5T(_5M,_6b,_6c);});},_6d=[0,_5H,_5E,_6a],_6e=new T(function(){return [0,_4x,_6d,_6f,_4J,_5E];}),_6f=function(_6g){return [0,_6e,_6g];},_6h=[0],_6i=7,_6j=function(_6k){return [0,_6h,_6i,_2W,_6k,_6h,_6h];},_6l=function(_6m,_){var _6n=new T(function(){var _6o=new T(function(){return B(_6j(_6m));});return B(_6f(_6o));});return new F(function(){return die(_6n);});},_6p=[0,_4m,_4n,_4i,_4g,_6l],_6q=[0,_6p,_q],_6r=[0,_6q,_4g],_6s=function(_6t,_6u,_6v,_6w,_6x,_6y,_6z,_6A){if(_6t!=_6x){return false;}else{if(E(_6u)!=E(_6y)){return false;}else{var _6B=E(_6v),_6C=E(_6z);if(E(_6B[1])!=E(_6C[1])){return false;}else{if(E(_6B[2])!=E(_6C[2])){return false;}else{return new F(function(){return _1N(_6w,_6A);});}}}}},_6D=function(_6E,_6F){var _6G=E(_6E),_6H=E(_6G[1]),_6I=E(_6F),_6J=E(_6I[1]);return new F(function(){return _6s(E(_6H[1]),_6H[2],_6G[2],_6G[3],E(_6J[1]),_6J[2],_6I[2],_6I[3]);});},_6K="scans",_6L=[1,_6K,_2W],_6M="calib",_6N=[1,_6M,_6L],_6O=function(_6P){var _6Q=E(_6P),_6R=_6Q[1],_6S=_6Q[2],_6T=new T(function(){return B(_2l(_6S));}),_6U=new T(function(){return B(_2l(_6R));});return [3,[1,_6U,[1,_6T,_2W]]];},_6V=new T(function(){return [1,"Dragging"];}),_6W=[0,_1A,_6V],_6X=new T(function(){return [1,"Free"];}),_6Y="state",_6Z=[0,_6Y,_6X],_70=[1,_6Z,_2W],_71=[4,E(_70)],_72=function(_73,_74){switch(E(_73)){case 0:return new F(function(){return _G(_1L,_74);});break;case 1:return new F(function(){return _G(_1M,_74);});break;case 2:return new F(function(){return _G(_1J,_74);});break;default:return new F(function(){return _G(_1K,_74);});}},_75=function(_76){return E(toJSStr(B(_72(_76,_2W))));},_77=function(_78){return [1,B(_75(_78))];},_79=function(_7a){var _7b=new T(function(){var _7c=E(E(_7a)[2]),_7d=_7c[1],_7e=_7c[2],_7f=_7c[3],_7g=_7c[4],_7h=new T(function(){return B(_6O(_7g));}),_7i=new T(function(){return B(_6O(_7f));}),_7j=new T(function(){return B(_6O(_7e));}),_7k=new T(function(){return B(_6O(_7d));});return [3,[1,_7k,[1,_7j,[1,_7i,[1,_7h,_2W]]]]];}),_7l=new T(function(){var _7m=E(E(_7a)[1]);if(!_7m[0]){return E(_71);}else{var _7n=_7m[1],_7o=new T(function(){return B(_77(_7n));});return [4,[1,_6W,[1,[0,_1v,_7o],_2W]]];}});return [1,[0,_1u,_7l],[1,[0,_1t,_7b],_2W]];},_7p="mouse",_7q="scans",_7r="fileName",_7s="rotations",_7t=[1,_7s,_2W],_7u=[1,_7r,_7t],_7v=[1,_7q,_7u],_7w=[1,_7p,_7v],_7x=function(_7y,_7z){var _7A=E(_7y);if(!_7A[0]){return [0];}else{var _7B=_7A[2],_7C=E(_7z);if(!_7C[0]){return [0];}else{var _7D=_7C[2],_7E=new T(function(){return B(_7x(_7B,_7D));});return [1,[0,_7A[1],_7C[1]],_7E];}}},_7F=function(_7G){var _7H=new T(function(){return [3,E(B(_1d(_2l,E(_7G)[4])))];}),_7I=new T(function(){return [1,toJSStr(E(E(_7G)[3]))];}),_7J=new T(function(){return [3,E(B(_1d(_3c,E(_7G)[2])))];}),_7K=new T(function(){if(!E(E(_7G)[1])){return [1,toJSStr(E(_2v))];}else{return [1,toJSStr(E(_2w))];}});return new F(function(){return _7x(_7w,[1,_7K,[1,_7J,[1,_7I,[1,_7H,_2W]]]]);});},_7L=function(_7M){return [1,E(_7M)];},_7N="deltaZ",_7O="deltaY",_7P="deltaX",_7Q=function(_7R,_7S){var _7T=jsShowI(_7R);return new F(function(){return _G(fromJSStr(_7T),_7S);});},_7U=41,_7V=40,_7W=function(_7X,_7Y,_7Z){if(_7Y>=0){return new F(function(){return _7Q(_7Y,_7Z);});}else{if(_7X<=6){return new F(function(){return _7Q(_7Y,_7Z);});}else{var _80=new T(function(){var _81=jsShowI(_7Y);return B(_G(fromJSStr(_81),[1,_7U,_7Z]));});return [1,_7V,_80];}}},_82=new T(function(){return B(unCStr(")"));}),_83=new T(function(){return B(_7W(0,2,_82));}),_84=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_83));}),_85=function(_86){var _87=new T(function(){return B(_7W(0,_86,_84));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_87)));});},_88=function(_89,_){return new T(function(){var _8a=Number(E(_89)),_8b=jsTrunc(_8a);if(_8b<0){return B(_85(_8b));}else{if(_8b>2){return B(_85(_8b));}else{return _8b;}}});},_8c=0,_8d=[0,_8c,_8c,_8c],_8e="button",_8f=new T(function(){return jsGetMouseCoords;}),_8g=function(_8h,_){var _8i=E(_8h);if(!_8i[0]){return _2W;}else{var _8j=_8i[1],_8k=B(_8g(_8i[2],_)),_8l=new T(function(){var _8m=Number(E(_8j));return jsTrunc(_8m);});return [1,_8l,_8k];}},_8n=function(_8o,_){var _8p=__arr2lst(0,_8o);return new F(function(){return _8g(_8p,_);});},_8q=function(_8r,_){return new F(function(){return _8n(E(_8r),_);});},_8s=function(_8t,_){return new T(function(){var _8u=Number(E(_8t));return jsTrunc(_8u);});},_8v=[0,_8s,_8q],_8w=function(_8x,_){var _8y=E(_8x);if(!_8y[0]){return _2W;}else{var _8z=B(_8w(_8y[2],_));return [1,_8y[1],_8z];}},_8A=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_8B=[0,_6h,_6i,_2W,_8A,_6h,_6h],_8C=new T(function(){return B(_6f(_8B));}),_8D=function(_){return new F(function(){return die(_8C);});},_8E=function(_8F){return E(E(_8F)[1]);},_8G=function(_8H,_8I,_8J,_){var _8K=__arr2lst(0,_8J),_8L=B(_8w(_8K,_)),_8M=E(_8L);if(!_8M[0]){return new F(function(){return _8D(_);});}else{var _8N=E(_8M[2]);if(!_8N[0]){return new F(function(){return _8D(_);});}else{if(!E(_8N[2])[0]){var _8O=B(A(_8E,[_8H,_8M[1],_])),_8P=B(A(_8E,[_8I,_8N[1],_]));return [0,_8O,_8P];}else{return new F(function(){return _8D(_);});}}}},_8Q=function(_){return new F(function(){return __jsNull();});},_8R=function(_8S){var _8T=B(A(_8S,[_]));return E(_8T);},_8U=new T(function(){return B(_8R(_8Q));}),_8V=new T(function(){return E(_8U);}),_8W=function(_8X,_8Y,_){if(E(_8X)==7){var _8Z=E(_8f)(_8Y),_90=B(_8G(_8v,_8v,_8Z,_)),_91=_90,_92=_8Y[E(_7P)],_93=_92,_94=_8Y[E(_7O)],_95=_94,_96=_8Y[E(_7N)],_97=_96;return new T(function(){return [0,E(_91),E(_6h),[0,_93,_95,_97]];});}else{var _98=E(_8f)(_8Y),_99=B(_8G(_8v,_8v,_98,_)),_9a=_99,_9b=_8Y[E(_8e)],_9c=__eq(_9b,E(_8V));if(!E(_9c)){var _9d=B(_88(_9b,_)),_9e=_9d;return new T(function(){return [0,E(_9a),[1,_9e],E(_8d)];});}else{return new T(function(){return [0,E(_9a),E(_6h),E(_8d)];});}}},_9f=function(_9g,_9h,_){return new F(function(){return _8W(_9g,E(_9h),_);});},_9i="mouseout",_9j="mouseover",_9k="mousemove",_9l="mouseup",_9m="mousedown",_9n="dblclick",_9o="click",_9p="wheel",_9q=function(_9r){switch(E(_9r)){case 0:return E(_9o);case 1:return E(_9n);case 2:return E(_9m);case 3:return E(_9l);case 4:return E(_9k);case 5:return E(_9j);case 6:return E(_9i);default:return E(_9p);}},_9s=[0,_9q,_9f],_9t=function(_){return new F(function(){return jsCreateElem("th");});},_9u=function(_9v,_9w){var _9x=function(_){return new F(function(){return jsCreateTextNode(toJSStr(E(_9w)));});};return new F(function(){return A(_1,[_9v,_9x]);});},_9y=function(_9z){return E(E(_9z)[1]);},_9A=function(_9B){return E(E(_9B)[3]);},_9C=function(_9D){return E(E(_9D)[2]);},_9E=function(_9F){return E(E(_9F)[4]);},_9G=function(_9H){return E(E(_9H)[1]);},_9I=function(_9J,_9K,_9L,_9M){var _9N=new T(function(){return B(A(_9G,[_9J,_9L]));}),_9O=function(_9P,_){var _9Q=E(_9P);if(!_9Q[0]){return _9;}else{var _9R=E(_9N),_9S=jsAppendChild(E(_9Q[1]),_9R),_9T=_9Q[2],_=_;while(1){var _9U=E(_9T);if(!_9U[0]){return _9;}else{var _9V=jsAppendChild(E(_9U[1]),_9R);_9T=_9U[2];continue;}}}},_9W=function(_9X,_){while(1){var _9Y=(function(_9Z,_){var _a0=E(_9Z);if(!_a0[0]){return _9;}else{var _a1=_a0[2],_a2=E(_a0[1]);if(!_a2[0]){var _a3=_a2[2],_a4=E(_a2[1]);switch(_a4[0]){case 0:var _a5=E(_9N),_a6=jsSet(_a5,_a4[1],_a3),_a7=_a1,_=_;while(1){var _a8=E(_a7);if(!_a8[0]){return _9;}else{var _a9=_a8[2],_aa=E(_a8[1]);if(!_aa[0]){var _ab=_aa[2],_ac=E(_aa[1]);switch(_ac[0]){case 0:var _ad=jsSet(_a5,_ac[1],_ab);_a7=_a9;continue;case 1:var _ae=jsSetStyle(_a5,_ac[1],_ab);_a7=_a9;continue;default:var _af=jsSetAttr(_a5,_ac[1],_ab);_a7=_a9;continue;}}else{var _ag=B(_9O(_aa[1],_));_a7=_a9;continue;}}}break;case 1:var _ah=E(_9N),_ai=jsSetStyle(_ah,_a4[1],_a3),_aj=_a1,_=_;while(1){var _ak=E(_aj);if(!_ak[0]){return _9;}else{var _al=_ak[2],_am=E(_ak[1]);if(!_am[0]){var _an=_am[2],_ao=E(_am[1]);switch(_ao[0]){case 0:var _ap=jsSet(_ah,_ao[1],_an);_aj=_al;continue;case 1:var _aq=jsSetStyle(_ah,_ao[1],_an);_aj=_al;continue;default:var _ar=jsSetAttr(_ah,_ao[1],_an);_aj=_al;continue;}}else{var _as=B(_9O(_am[1],_));_aj=_al;continue;}}}break;default:var _at=E(_9N),_au=jsSetAttr(_at,_a4[1],_a3),_av=_a1,_=_;while(1){var _aw=E(_av);if(!_aw[0]){return _9;}else{var _ax=_aw[2],_ay=E(_aw[1]);if(!_ay[0]){var _az=_ay[2],_aA=E(_ay[1]);switch(_aA[0]){case 0:var _aB=jsSet(_at,_aA[1],_az);_av=_ax;continue;case 1:var _aC=jsSetStyle(_at,_aA[1],_az);_av=_ax;continue;default:var _aD=jsSetAttr(_at,_aA[1],_az);_av=_ax;continue;}}else{var _aE=B(_9O(_ay[1],_));_av=_ax;continue;}}}}}else{var _aF=B(_9O(_a2[1],_));_9X=_a1;return null;}}})(_9X,_);if(_9Y!=null){return _9Y;}}},_aG=function(_){return new F(function(){return _9W(_9M,_);});};return new F(function(){return A(_1,[_9K,_aG]);});},_aH=function(_aI,_aJ,_aK,_aL){var _aM=B(_9y(_aJ)),_aN=function(_aO){var _aP=new T(function(){return B(A(_9E,[_aM,_aO]));}),_aQ=new T(function(){return B(_9I(_aI,_aJ,_aO,_aL));});return new F(function(){return A(_9A,[_aM,_aQ,_aP]);});};return new F(function(){return A(_9C,[_aM,_aK,_aN]);});},_aR=function(_aS,_){var _aT=E(_aS);if(!_aT[0]){return _2W;}else{var _aU=B(A(_9u,[_6q,_aT[1],_])),_aV=B(A(_aH,[_s,_6q,_9t,[1,[1,[1,_aU,_2W]],_2W],_])),_aW=B(_aR(_aT[2],_));return [1,_aV,_aW];}},_aX=function(_aY,_aZ,_){var _b0=B(A(_9u,[_6q,_aY,_])),_b1=B(A(_aH,[_s,_6q,_9t,[1,[1,[1,_b0,_2W]],_2W],_])),_b2=B(_aR(_aZ,_));return [1,_b1,_b2];},_b3=function(_){return new F(function(){return jsCreateElem("td");});},_b4=function(_b5,_b6,_){var _b7=jsShow(_b5),_b8=jsCreateTextNode(toJSStr(fromJSStr(_b7))),_b9=B(A(_aH,[_s,_6q,_b3,[1,[1,[1,_b8,_2W]],_2W],_])),_ba=B(A(_b6,[_]));return [1,_b9,_ba];},_bb=function(_bc,_bd){return [0,E(_bc),toJSStr(E(_bd))];},_be=2,_bf=0,_bg=function(_){return new F(function(){return jsCreateElem("input");});},_bh=new T(function(){return B(unCStr("x1"));}),_bi=function(_){return new F(function(){return jsCreateElem("tr");});},_bj=new T(function(){return B(unCStr("y1"));}),_bk=new T(function(){return B(unCStr("x2"));}),_bl=new T(function(){return B(unCStr("y2"));}),_bm=new T(function(){return B(unCStr("title"));}),_bn=new T(function(){return B(unCStr("Delete"));}),_bo=[1,_bn,_2W],_bp=[1,_bm,_bo],_bq=[1,_bl,_bp],_br=[1,_bk,_bq],_bs=[1,_bj,_br],_bt=function(_){return new F(function(){return jsCreateElem("span");});},_bu=new T(function(){return [0,[2,"class"],"glyphicon glyphicon-remove"];}),_bv=[1,_bu,_2W],_bw=new T(function(){return B(_aH(_s,_6q,_bt,_bv));}),_bx=function(_by,_){var _bz=E(_by);if(!_bz[0]){return _2W;}else{var _bA=B(A(_aH,[_s,_6q,_b3,[1,[1,[1,_bz[1],_2W]],_2W],_])),_bB=B(_bx(_bz[2],_));return [1,_bA,_bB];}},_bC=function(_){return new F(function(){return jsCreateElem("button");});},_bD=new T(function(){return [2,"value"];}),_bE=function(_){return _2W;},_bF=new T(function(){return [0,[2,"type"],"text"];}),_bG=new T(function(){return [0,[2,"class"],"btn btn-danger"];}),_bH=function(_bI){return E(E(_bI)[1]);},_bJ=function(_bK){return E(E(_bK)[2]);},_bL=function(_bM){return E(E(_bM)[1]);},_bN=function(_){return new F(function(){return nMV(_6h);});},_bO=new T(function(){return B(_8R(_bN));}),_bP=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_bQ=function(_bR){return E(E(_bR)[2]);},_bS=function(_bT,_bU,_bV,_bW,_bX,_bY){var _bZ=B(_bH(_bT)),_c0=B(_9y(_bZ)),_c1=new T(function(){return B(_1(_bZ));}),_c2=new T(function(){return B(_9E(_c0));}),_c3=new T(function(){return B(A(_9G,[_bU,_bW]));}),_c4=new T(function(){return B(A(_bL,[_bV,_bX]));}),_c5=function(_c6){return new F(function(){return A(_c2,[[0,_c4,_c3,_c6]]);});},_c7=function(_c8){var _c9=new T(function(){var _ca=new T(function(){var _cb=E(_c3),_cc=E(_c4),_cd=E(_c8),_ce=function(_cf,_){var _cg=B(A(_cd,[_cf,_]));return _8V;},_ch=__createJSFunc(2,E(_ce)),_ci=_ch,_cj=function(_){return new F(function(){return E(_bP)(_cb,_cc,_ci);});};return E(_cj);});return B(A(_c1,[_ca]));});return new F(function(){return A(_9C,[_c0,_c9,_c5]);});},_ck=new T(function(){var _cl=new T(function(){return B(_1(_bZ));}),_cm=function(_cn){var _co=new T(function(){var _cp=function(_){var _=wMV(E(_bO),[1,_cn]);return new F(function(){return A(_bJ,[_bV,_bX,_cn,_]);});};return B(A(_cl,[_cp]));});return new F(function(){return A(_9C,[_c0,_co,_bY]);});};return B(A(_bQ,[_bT,_cm]));});return new F(function(){return A(_9C,[_c0,_ck,_c7]);});},_cq=function(_cr,_cs){while(1){var _ct=E(_cr);if(!_ct[0]){return E(_cs);}else{_cr=_ct[2];var _cu=[1,_ct[1],_cs];_cs=_cu;continue;}}},_cv=function(_cw,_cx,_cy,_cz,_){var _cA=jsClearChildren(_cz),_cB=B(_aX(_bh,_bs,_)),_cC=_cB,_cD=new T(function(){return B(_7L(_cC));}),_cE=B(A(_aH,[_s,_6q,_bi,[1,_cD,_2W],_])),_cF=jsAppendChild(E(_cE),_cz),_cG=function(_cH,_){var _cI=E(_cH);if(!_cI[0]){return _2W;}else{var _cJ=E(_cI[1]),_cK=_cJ[3],_cL=E(_cJ[1]),_cM=_cL[2],_cN=E(_cJ[2]),_cO=_cN[1],_cP=_cN[2],_cQ=function(_){var _cR=function(_){var _cS=function(_){return new F(function(){return _b4(E(_cP)*25/900,_bE,_);});};return new F(function(){return _b4(E(_cO)*25/900,_cS,_);});};return new F(function(){return _b4(E(_cM)*25/900,_cR,_);});},_cT=B(_b4(E(_cL[1])*25/900,_cQ,_)),_cU=B(_bx(_cT,_)),_cV=_cU,_cW=new T(function(){return B(_7L(_cV));}),_cX=B(A(_aH,[_s,_6q,_bi,[1,_cW,_2W],_])),_cY=new T(function(){return B(_bb(_bD,_cK));}),_cZ=B(A(_aH,[_s,_6q,_bg,[1,_bF,[1,_cY,_2W]],_])),_d0=_cZ,_d1=B(A(_bw,[_])),_d2=B(A(_aH,[_s,_6q,_bC,[1,_bG,[1,[1,[1,_d1,_2W]],_2W]],_])),_d3=B(A(_aH,[_s,_6q,_b3,[1,[1,[1,_d0,_2W]],_2W],_])),_d4=E(_cX),_d5=jsAppendChild(E(_d3),_d4),_d6=E(_d2),_d7=jsAppendChild(_d6,_d4),_d8=new T(function(){return B(A(_cx,[_cJ]));}),_d9=function(_da){return E(_d8);},_db=B(A(_bS,[_6r,_s,_9s,_d6,_bf,_d9,_])),_dc=new T(function(){return B(A(_cw,[_d0,_cJ]));}),_dd=function(_de){return E(_dc);},_df=B(A(_bS,[_6r,_s,_n,_d0,_be,_dd,_])),_dg=jsAppendChild(_d4,_cz),_dh=B(_cG(_cI[2],_));return [1,_9,_dh];}},_di=B(_cG(B(_cq(E(_cy)[2],_2W)),_));return _9;},_dj=function(_dk,_dl,_dm,_dn,_){var _do=jsPushState(_dn),_dp=jsScale(_dn,_dk,_dl),_dq=B(A(_dm,[_dn,_])),_dr=jsPopState(_dn);return _9;},_ds=function(_dt,_du,_){var _dv=jsBeginPath(_du),_dw=B(A(_dt,[_du,_])),_dx=jsStroke(_du);return _9;},_dy=",",_dz="[",_dA="]",_dB="{",_dC="}",_dD=":",_dE="\"",_dF="true",_dG="false",_dH="null",_dI=function(_dJ){return new F(function(){return jsStringify(E(_dJ));});},_dK=function(_dL){return new F(function(){return _dI(_dL);});},_dM=function(_dN,_dO){var _dP=E(_dO);switch(_dP[0]){case 0:var _dQ=_dP[1],_dR=new T(function(){return jsShow(_dQ);});return [0,_dR,_dN];case 1:var _dS=_dP[1],_dT=new T(function(){return jsStringify(_dS);});return [0,_dT,_dN];case 2:return (!E(_dP[1]))?[0,_dG,_dN]:[0,_dF,_dN];case 3:var _dU=E(_dP[1]);if(!_dU[0]){return [0,_dz,[1,_dA,_dN]];}else{var _dV=_dU[1],_dW=_dU[2],_dX=new T(function(){var _dY=new T(function(){var _dZ=[1,_dA,_dN],_e0=function(_e1){var _e2=E(_e1);if(!_e2[0]){return E(_dZ);}else{var _e3=_e2[1],_e4=_e2[2],_e5=new T(function(){var _e6=new T(function(){return B(_e0(_e4));}),_e7=B(_dM(_e6,_e3));return [1,_e7[1],_e7[2]];});return [1,_dy,_e5];}};return B(_e0(_dW));}),_e8=B(_dM(_dY,_dV));return [1,_e8[1],_e8[2]];});return [0,_dz,_dX];}break;case 4:var _e9=E(_dP[1]);if(!_e9[0]){return [0,_dB,[1,_dC,_dN]];}else{var _ea=_e9[2],_eb=E(_e9[1]),_ec=_eb[1],_ed=_eb[2],_ee=new T(function(){var _ef=new T(function(){var _eg=[1,_dC,_dN],_eh=function(_ei){var _ej=E(_ei);if(!_ej[0]){return E(_eg);}else{var _ek=_ej[2],_el=E(_ej[1]),_em=_el[2],_en=new T(function(){var _eo=new T(function(){return B(_eh(_ek));}),_ep=B(_dM(_eo,_em));return [1,_ep[1],_ep[2]];});return [1,_dy,[1,_dE,[1,_el[1],[1,_dE,[1,_dD,_en]]]]];}};return B(_eh(_ea));}),_eq=B(_dM(_ef,_ed));return [1,_eq[1],_eq[2]];}),_er=new T(function(){return B(_dK(_ec));});return [0,_dB,[1,_er,[1,_dD,_ee]]];}break;default:return [0,_dH,_dN];}},_es=new T(function(){return toJSStr(_2W);}),_et=function(_eu){var _ev=B(_dM(_2W,_eu)),_ew=jsCat([1,_ev[1],_ev[2]],E(_es));return E(_ew);},_ex=function(_ey,_ez){return (E(_ey)!=E(_ez))?true:false;},_eA=function(_eB,_eC){return E(_eB)==E(_eC);},_eD=[0,_eA,_ex],_eE=function(_eF,_eG){var _eH=E(_eF),_eI=E(_eH[1]),_eJ=E(_eG),_eK=E(_eJ[1]);if(E(_eI[1])!=E(_eK[1])){return true;}else{if(E(_eI[2])!=E(_eK[2])){return true;}else{var _eL=E(_eH[2]),_eM=E(_eJ[2]);return (E(_eL[1])!=E(_eM[1]))?true:(E(_eL[2])!=E(_eM[2]))?true:(!B(_1N(_eH[3],_eJ[3])))?true:false;}}},_eN=[0,_6D,_eE],_eO=function(_eP,_eQ,_eR){while(1){var _eS=E(_eQ);if(!_eS[0]){return (E(_eR)[0]==0)?true:false;}else{var _eT=E(_eR);if(!_eT[0]){return false;}else{if(!B(A(_t,[_eP,_eS[1],_eT[1]]))){return false;}else{_eQ=_eS[2];_eR=_eT[2];continue;}}}}},_eU=function(_eV){while(1){var _eW=E(_eV);if(!_eW[0]){return false;}else{if(E(_eW[1])==32){return true;}else{_eV=_eW[2];continue;}}}},_eX=function(_eY,_eZ){if(E(_eY)==32){return true;}else{return new F(function(){return _eU(_eZ);});}},_f0=function(_f1){while(1){var _f2=E(_f1);if(!_f2[0]){return false;}else{var _f3=E(_f2[1]);if(!_f3[0]){return true;}else{if(!B(_eX(_f3[1],_f3[2]))){_f1=_f2[2];continue;}else{return true;}}}}},_f4=function(_f5){return E(E(_f5)[3]);},_f6=function(_f7,_f8,_f9){return (!B(_eO(_eN,_f7,_2W)))?(!B(_f0(B(_1d(_f4,_f7)))))?(!B(_1N(_f8,_2W)))?(!B(_eO(_eD,_f9,_2W)))?true:false:false:false:false;},_fa=function(_fb,_fc){var _fd=function(_){return new F(function(){return jsFind(toJSStr(E(_fc)));});};return new F(function(){return A(_1,[_fb,_fd]);});},_fe=new T(function(){return encodeURIComponent;}),_ff=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:172:3-9"));}),_fg=[0,_6h,_6i,_2W,_ff,_6h,_6h],_fh=new T(function(){return B(_6f(_fg));}),_fi=new T(function(){return B(unCStr("href"));}),_fj=new T(function(){return B(unCStr("data:text/plain;charset=utf-8,"));}),_fk=function(_fl,_fm,_fn,_fo,_fp){var _fq=function(_){var _fr=jsSetAttr(B(A(_9G,[_fl,_fn])),toJSStr(E(_fo)),toJSStr(E(_fp)));return _9;};return new F(function(){return A(_1,[_fm,_fq]);});},_fs=function(_ft,_fu,_){var _fv=B(A(_fa,[_6q,_ft,_])),_fw=E(_fv);if(!_fw[0]){return new F(function(){return die(_fh);});}else{var _fx=E(_fe)(toJSStr(_fu)),_fy=_fx,_fz=new T(function(){var _fA=new T(function(){var _fB=String(_fy);return fromJSStr(_fB);},1);return B(_G(_fj,_fA));});return new F(function(){return A(_fk,[_s,_6q,_fw[1],_fi,_fz,_]);});}},_fC=function(_fD,_fE,_fF,_){var _fG=jsPushState(_fF),_fH=jsRotate(_fF,_fD),_fI=B(A(_fE,[_fF,_])),_fJ=jsPopState(_fF);return _9;},_fK=function(_fL,_fM,_fN,_fO,_){var _fP=jsPushState(_fO),_fQ=jsTranslate(_fO,_fL,_fM),_fR=B(A(_fN,[_fO,_])),_fS=jsPopState(_fO);return _9;},_fT=function(_fU,_fV){if(_fV<=0){var _fW=function(_fX){var _fY=function(_fZ){var _g0=function(_g1){var _g2=function(_g3){var _g4=isDoubleNegativeZero(_fV),_g5=_g4,_g6=function(_g7){var _g8=E(_fU);if(!_g8){return (_fV>=0)?(E(_g5)==0)?E(_fV):3.141592653589793:3.141592653589793;}else{var _g9=E(_fV);return (_g9==0)?E(_g8):_g9+_g8;}};if(!E(_g5)){return new F(function(){return _g6(_);});}else{var _ga=E(_fU),_gb=isDoubleNegativeZero(_ga);if(!E(_gb)){return new F(function(){return _g6(_);});}else{return  -B(_fT( -_ga,_fV));}}};if(_fV>=0){return new F(function(){return _g2(_);});}else{var _gc=E(_fU),_gd=isDoubleNegativeZero(_gc);if(!E(_gd)){return new F(function(){return _g2(_);});}else{return  -B(_fT( -_gc,_fV));}}};if(_fV>0){return new F(function(){return _g0(_);});}else{var _ge=E(_fU);if(_ge>=0){return new F(function(){return _g0(_);});}else{return  -B(_fT( -_ge,_fV));}}};if(_fV>=0){return new F(function(){return _fY(_);});}else{var _gf=E(_fU);if(_gf<=0){return new F(function(){return _fY(_);});}else{return 3.141592653589793+Math.atan(_gf/_fV);}}};if(!E(_fV)){if(E(_fU)<=0){return new F(function(){return _fW(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _fW(_);});}}else{return new F(function(){return Math.atan(E(_fU)/_fV);});}},_gg=function(_gh,_gi){return E(_gh)-E(_gi);},_gj=function(_gk,_gl,_gm,_gn,_go,_gp,_gq,_gr){var _gs=new T(function(){return B(_gg(_gn,_gl));}),_gt=new T(function(){return B(_gg(_gp,_gn));}),_gu=new T(function(){return B(_gg(_gr,_gp));}),_gv=new T(function(){return B(_gg(_gl,_gr));});return new F(function(){return Math.atan((Math.tan(B(_fT(_gs,_gm-_gk))-1.5707963267948966)+Math.tan(B(_fT(_gt,_go-_gm)))+Math.tan(B(_fT(_gu,_gq-_go))+1.5707963267948966)+Math.tan(B(_fT(_gv,_gk-_gq))-3.141592653589793))/4);});},_gw=function(_gx){return E(_gx)/2;},_gy=function(_gz,_gA,_gB,_){var _gC=E(_gz);return new F(function(){return _fK(E(_gC[1]),E(_gC[2]),_gA,E(_gB),_);});},_gD=function(_gE,_gF){var _gG=new T(function(){var _gH=E(_gE),_gI=E(E(_gF)[2]),_gJ=E(_gI[1]),_gK=E(_gJ[1]),_gL=E(_gJ[2]),_gM=E(_gI[2]),_gN=E(_gM[1]),_gO=E(_gM[2]),_gP=E(_gI[3]),_gQ=E(_gP[1]),_gR=E(_gP[2]),_gS=E(_gI[4]),_gT=E(_gS[1]),_gU=E(_gS[2]);return Math.sqrt(E(_gH[1])*E(_gH[2])/(0.5*(_gK*_gU+_gT*_gR+_gQ*_gL-_gK*_gR-_gQ*_gU-_gT*_gL)+0.5*(_gT*_gR+_gQ*_gO+_gN*_gU-_gT*_gO-_gN*_gR-_gQ*_gU)));}),_gV=new T(function(){var _gW=E(_gE),_gX=_gW[1],_gY=_gW[2],_gZ=new T(function(){return B(_gw(_gY));}),_h0=new T(function(){return B(_gw(_gX));});return [0,_h0,_gZ];}),_h1=new T(function(){var _h2=E(E(_gF)[2]),_h3=E(_h2[1]),_h4=E(_h2[2]),_h5=E(_h2[3]),_h6=E(_h2[4]);return  -B(_gj(E(_h3[1]),_h3[2],E(_h4[1]),_h4[2],E(_h5[1]),_h5[2],E(_h6[1]),_h6[2]));}),_h7=new T(function(){var _h8=E(E(_gF)[2]),_h9=E(_h8[1]),_ha=_h9[1],_hb=_h9[2],_hc=E(_h8[2]),_hd=_hc[1],_he=_hc[2],_hf=E(_h8[3]),_hg=_hf[1],_hh=_hf[2],_hi=E(_h8[4]),_hj=_hi[1],_hk=_hi[2],_hl=new T(function(){return (E(_hb)+E(_he)+E(_hh)+E(_hk))/4/(-1);}),_hm=new T(function(){return (E(_ha)+E(_hd)+E(_hg)+E(_hj))/4/(-1);});return [0,_hm,_hl];}),_hn=function(_ho,_hp,_){var _hq=E(_gV),_hr=function(_hs,_){var _ht=E(_gG),_hu=function(_hv,_){var _hw=function(_hx,_){return new F(function(){return _gy(_h7,_ho,_hx,_);});};return new F(function(){return _fC(E(_h1),_hw,E(_hv),_);});};return new F(function(){return _dj(_ht,_ht,_hu,E(_hs),_);});};return new F(function(){return _fK(E(_hq[1]),E(_hq[2]),_hr,E(_hp),_);});};return E(_hn);},_hy=function(_hz,_hA,_){var _hB=E(_hz);if(!_hB[0]){return _9;}else{var _hC=E(_hB[1]),_hD=E(_hA),_hE=jsMoveTo(_hD,E(_hC[1]),E(_hC[2])),_hF=_hB[2],_=_;while(1){var _hG=E(_hF);if(!_hG[0]){return _9;}else{var _hH=E(_hG[1]),_hI=jsLineTo(_hD,E(_hH[1]),E(_hH[2]));_hF=_hG[2];continue;}}}},_hJ=function(_hK,_hL,_){var _hM=new T(function(){return E(E(_hK)[2]);}),_hN=new T(function(){return E(E(_hM)[1]);}),_hO=new T(function(){return E(E(_hM)[4]);}),_hP=new T(function(){return E(E(_hM)[3]);}),_hQ=new T(function(){return E(E(_hM)[2]);});return new F(function(){return _hy([1,_hN,[1,_hQ,[1,_hP,[1,_hO,[1,_hN,_2W]]]]],_hL,_);});},_hR=",",_hS="rgba(",_hT=new T(function(){return toJSStr(_2W);}),_hU="rgb(",_hV=")",_hW=[1,_hV,_2W],_hX=function(_hY){var _hZ=E(_hY);if(!_hZ[0]){var _i0=_hZ[1],_i1=_hZ[2],_i2=_hZ[3],_i3=new T(function(){return String(_i2);}),_i4=new T(function(){return String(_i1);}),_i5=new T(function(){return String(_i0);}),_i6=jsCat([1,_hU,[1,_i5,[1,_hR,[1,_i4,[1,_hR,[1,_i3,_hW]]]]]],E(_hT));return E(_i6);}else{var _i7=_hZ[4],_i8=_hZ[1],_i9=_hZ[2],_ia=_hZ[3],_ib=new T(function(){return String(_i7);}),_ic=new T(function(){return String(_ia);}),_id=new T(function(){return String(_i9);}),_ie=new T(function(){return String(_i8);}),_if=jsCat([1,_hS,[1,_ie,[1,_hR,[1,_id,[1,_hR,[1,_ic,[1,_hR,[1,_ib,_hW]]]]]]]],E(_hT));return E(_if);}},_ig="strokeStyle",_ih="fillStyle",_ii=function(_ij,_ik){var _il=new T(function(){return B(_hX(_ij));}),_im=function(_in,_){var _io=E(_in),_ip=E(_ih),_iq=jsGet(_io,_ip),_ir=E(_ig),_is=jsGet(_io,_ir),_it=E(_il),_iu=jsSet(_io,_ip,_it),_iv=jsSet(_io,_ir,_it),_iw=B(A(_ik,[_io,_])),_ix=jsSet(_io,_ip,_iq),_iy=jsSet(_io,_ir,_is);return _9;};return E(_im);},_iz=function(_iA,_iB,_iC){var _iD=E(_iC);if(!_iD[0]){return [0];}else{var _iE=_iD[1],_iF=_iD[2];if(!B(A(_iA,[_iB,_iE]))){var _iG=new T(function(){return B(_iz(_iA,_iB,_iF));});return [1,_iE,_iG];}else{return E(_iF);}}},_iH=function(_iI){return E(E(_iI)[3]);},_iJ="lineWidth",_iK=function(_iL,_iM){var _iN=new T(function(){return String(E(_iL));}),_iO=function(_iP,_){var _iQ=E(_iP),_iR=E(_iJ),_iS=jsGet(_iQ,_iR),_iT=jsSet(_iQ,_iR,E(_iN)),_iU=B(A(_iM,[_iQ,_])),_iV=jsSet(_iQ,_iR,_iS);return _9;};return E(_iO);},_iW=new T(function(){return B(unCStr("saveLink"));}),_iX=new T(function(){return B(unCStr("exportLink"));}),_iY=[0,255,0,255],_iZ=1,_j0=900,_j1=[0,_j0,_j0],_j2=new T(function(){return B(unCStr("btn btn-primary"));}),_j3=new T(function(){return B(unCStr("class"));}),_j4=new T(function(){return B(unCStr("btn btn-primary disabled"));}),_j5=new T(function(){return B(unCStr("value"));}),_j6=function(_j7,_){var _j8=jsHasCtx2D(_j7);if(!E(_j8)){return _6h;}else{var _j9=jsGetCtx2D(_j7);return [1,[0,_j9,_j7]];}},_ja=function(_jb,_){return new F(function(){return _j6(E(_jb),_);});},_jc=function(_jd,_je){var _jf=function(_){var _jg=jsFind(toJSStr(E(_je)));if(!_jg[0]){return _6h;}else{return new F(function(){return _ja(_jg[1],_);});}};return new F(function(){return A(_1,[_jd,_jf]);});},_jh=new T(function(){return B(unCStr("aligned"));}),_ji=new T(function(){return B(_jc(_6q,_jh));}),_jj=new T(function(){return B(unCStr("original"));}),_jk=new T(function(){return B(_jc(_6q,_jj));}),_jl=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:150:3-8"));}),_jm=[0,_6h,_6i,_2W,_jl,_6h,_6h],_jn=new T(function(){return B(_6f(_jm));}),_jo=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:132:3-14"));}),_jp=[0,_6h,_6i,_2W,_jo,_6h,_6h],_jq=new T(function(){return B(_6f(_jp));}),_jr=new T(function(){return B(unCStr("runfile"));}),_js=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:131:3-10"));}),_jt=[0,_6h,_6i,_2W,_js,_6h,_6h],_ju=new T(function(){return B(_6f(_jt));}),_jv=new T(function(){return B(unCStr("scans"));}),_jw=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:130:3-11"));}),_jx=[0,_6h,_6i,_2W,_jw,_6h,_6h],_jy=new T(function(){return B(_6f(_jx));}),_jz=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:129:3-11"));}),_jA=[0,_6h,_6i,_2W,_jz,_6h,_6h],_jB=new T(function(){return B(_6f(_jA));}),_jC=function(_jD,_jE,_){while(1){var _jF=E(_jD);if(!_jF[0]){return _9;}else{var _jG=E(_jF[1]),_jH=B(_hy([1,_jG[1],[1,_jG[2],_2W]],_jE,_));_jD=_jF[2];continue;}}},_jI=[0,255,0,255],_jJ=1,_jK=function(_jL){var _jM=new T(function(){var _jN=new T(function(){var _jO=E(_jL)[2];return function(_jP,_jQ){return new F(function(){return _jC(_jO,_jP,_jQ);});};}),_jR=function(_jS,_){return new F(function(){return _ds(_jN,E(_jS),_);});};return B(_ii(_jI,_jR));});return new F(function(){return _iK(_jJ,_jM);});},_jT=function(_jU,_jV,_jW,_jX,_jY){var _jZ=function(_){var _k0=jsSet(B(A(_9G,[_jU,_jW])),toJSStr(E(_jX)),toJSStr(E(_jY)));return _9;};return new F(function(){return A(_1,[_jV,_jZ]);});},_k1=function(_k2){while(1){var _k3=E(_k2);if(!_k3[0]){_k2=[1,I_fromInt(_k3[1])];continue;}else{return new F(function(){return I_toString(_k3[1]);});}}},_k4=function(_k5,_k6){return new F(function(){return _G(fromJSStr(B(_k1(_k5))),_k6);});},_k7=function(_k8,_k9){var _ka=E(_k8);if(!_ka[0]){var _kb=_ka[1],_kc=E(_k9);return (_kc[0]==0)?_kb<_kc[1]:I_compareInt(_kc[1],_kb)>0;}else{var _kd=_ka[1],_ke=E(_k9);return (_ke[0]==0)?I_compareInt(_kd,_ke[1])<0:I_compare(_kd,_ke[1])<0;}},_kf=[0,0],_kg=function(_kh,_ki,_kj){if(_kh<=6){return new F(function(){return _k4(_ki,_kj);});}else{if(!B(_k7(_ki,_kf))){return new F(function(){return _k4(_ki,_kj);});}else{var _kk=new T(function(){return B(_G(fromJSStr(B(_k1(_ki))),[1,_7U,_kj]));});return [1,_7V,_kk];}}},_kl=function(_km){var _kn=E(_km);if(!_kn[0]){return [0];}else{var _ko=_kn[2],_kp=new T(function(){return B(_kl(_ko));},1);return new F(function(){return _G(_kn[1],_kp);});}},_kq=new T(function(){return B(unCStr("1"));}),_kr=[1,_kq,_2W],_ks=[1,_kq,_kr],_kt=new T(function(){return B(unCStr("ccdtrans"));}),_ku=new T(function(){return B(unCStr(" "));}),_kv=new T(function(){return B(unCStr("\r\n"));}),_kw=function(_kx,_ky){var _kz=E(_ky);if(!_kz[0]){return [0];}else{var _kA=_kz[2],_kB=new T(function(){return B(_kw(_kx,_kA));});return [1,_kx,[1,_kz[1],_kB]];}},_kC=new T(function(){return B(unCStr("0"));}),_kD=function(_kE,_kF,_kG,_kH,_kI,_kJ,_kK){var _kL=new T(function(){var _kM=new T(function(){var _kN=new T(function(){var _kO=jsShow(E(_kF)),_kP=new T(function(){var _kQ=new T(function(){var _kR=new T(function(){var _kS=new T(function(){return B(_7W(0,E(_kK),_2W));}),_kT=new T(function(){var _kU=jsShow(E(_kI));return fromJSStr(_kU);}),_kV=new T(function(){var _kW=jsShow(E(_kH));return fromJSStr(_kW);});return B(_kw(_ku,[1,_kG,[1,_kV,[1,_kT,[1,_kS,[1,_kC,[1,_kJ,_ks]]]]]]));});return B(_kl([1,_kt,_kR]));},1);return B(_G(_kv,_kQ));},1);return B(_G(fromJSStr(_kO),_kP));});return B(unAppCStr(" ",_kN));},1);return B(_G(_kE,_kM));});return new F(function(){return unAppCStr("umv ",_kL);});},_kX=function(_kY){var _kZ=I_decodeDouble(_kY);return [0,[1,_kZ[2]],_kZ[1]];},_l0=function(_l1){return [0,_l1];},_l2=function(_l3){var _l4=hs_intToInt64(2147483647),_l5=hs_leInt64(_l3,_l4);if(!_l5){return [1,I_fromInt64(_l3)];}else{var _l6=hs_intToInt64(-2147483648),_l7=hs_geInt64(_l3,_l6);if(!_l7){return [1,I_fromInt64(_l3)];}else{var _l8=hs_int64ToInt(_l3);return new F(function(){return _l0(_l8);});}}},_l9=function(_la){var _lb=hs_intToInt64(_la);return E(_lb);},_lc=function(_ld){var _le=E(_ld);if(!_le[0]){return new F(function(){return _l9(_le[1]);});}else{return new F(function(){return I_toInt64(_le[1]);});}},_lf=new T(function(){return B(_G(_kv,_kv));}),_lg=new T(function(){return B(unCStr("sav"));}),_lh=new T(function(){return B(unCStr("sah"));}),_li=function(_lj,_lk){while(1){var _ll=E(_lj);if(!_ll[0]){_lj=[1,I_fromInt(_ll[1])];continue;}else{return [1,I_shiftLeft(_ll[1],_lk)];}}},_lm=function(_ln){var _lo=new T(function(){var _lp=E(_ln),_lq=_lp[2],_lr=_lp[4],_ls=new T(function(){var _lt=new T(function(){var _lu=function(_lv){var _lw=new T(function(){var _lx=E(_lv),_ly=rintDouble(_lx*180/3.141592653589793),_lz=B(_kX(_ly)),_lA=_lz[1],_lB=_lz[2],_lC=new T(function(){var _lD=new T(function(){var _lE=Math.cos(_lx),_lF=function(_lG){var _lH=E(_lG),_lI=_lH[3],_lJ=E(_lH[1]),_lK=_lJ[2],_lL=E(_lH[2]),_lM=_lL[2],_lN=E(_lJ[1]),_lO=E(_lL[1]);if(_lN!=_lO){var _lP=new T(function(){var _lQ=(_lO-_lN)*25/900;if(!_lQ){var _lR=rintDouble(0);return _lR&4294967295;}else{if(_lQ<=0){var _lS=rintDouble( -_lQ/0.1);return _lS&4294967295;}else{var _lT=rintDouble(_lQ/0.1);return _lT&4294967295;}}},1),_lU=new T(function(){return E(_lK)*25/900;},1);return new F(function(){return _kD(_lg,_lU,_lh,12.5+(_lN*25/900-12.5)*_lE,12.5+(_lO*25/900-12.5)*_lE,_lI,_lP);});}else{var _lV=new T(function(){var _lW=(E(_lM)-E(_lK))*25/900;if(!_lW){var _lX=rintDouble(0);return _lX&4294967295;}else{if(_lW<=0){var _lY=rintDouble( -_lW/0.1);return _lY&4294967295;}else{var _lZ=rintDouble(_lW/0.1);return _lZ&4294967295;}}},1),_m0=new T(function(){return E(_lM)*25/900;},1),_m1=new T(function(){return E(_lK)*25/900;},1);return new F(function(){return _kD(_lh,12.5+(_lN*25/900-12.5)*_lE,_lg,_m1,_m0,_lI,_lV);});}},_m2=B(_1d(_lF,B(_cq(_lq,_2W))));if(!_m2[0]){return [0];}else{var _m3=_m2[2],_m4=new T(function(){return B(_kw(_kv,_m3));});return B(_kl([1,_m2[1],_m4]));}},1);return B(_G(_kv,_lD));});if(_lB>=0){return B(_G(B(_kg(0,B(_li(_lA,_lB)),_2W)),_lC));}else{var _m5=hs_uncheckedIShiftRA64(B(_lc(_lA)), -_lB);return B(_G(B(_kg(0,B(_l2(_m5)),_2W)),_lC));}});return new F(function(){return unAppCStr("umv sar ",_lw);});},_m6=B(_1d(_lu,_lr));if(!_m6[0]){return [0];}else{var _m7=_m6[2],_m8=new T(function(){return B(_kw(_lf,_m7));});return B(_kl([1,_m6[1],_m8]));}},1);return B(_G(_kv,_lt));},1);return B(_G(_lp[3],_ls));});return new F(function(){return unAppCStr("ccdnewfile ",_lo);});},_m9=function(_ma){return new F(function(){return fromJSStr(E(_ma));});},_mb=function(_mc,_md,_me,_mf){var _mg=function(_){return new F(function(){return jsGet(B(A(_9G,[_mc,_me])),E(_mf));});};return new F(function(){return A(_1,[_md,_mg]);});},_mh=function(_mi,_mj,_mk,_ml){var _mm=B(_9y(_mj)),_mn=new T(function(){return B(_9E(_mm));}),_mo=function(_mp){var _mq=new T(function(){return B(_m9(_mp));});return new F(function(){return A(_mn,[_mq]);});},_mr=new T(function(){var _ms=new T(function(){return toJSStr(E(_ml));});return B(_mb(_mi,_mj,_mk,_ms));});return new F(function(){return A(_9C,[_mm,_mr,_mo]);});},_mt=new T(function(){return B(unCStr("value"));}),_mu=function(_mv,_mw,_mx){var _my=E(_mx);if(!_my[0]){return [0];}else{var _mz=_my[1],_mA=_my[2];if(!B(A(_mv,[_mz]))){var _mB=new T(function(){return B(_mu(_mv,_mw,_mA));});return [1,_mz,_mB];}else{var _mC=new T(function(){return B(_mu(_mv,_mw,_mA));}),_mD=new T(function(){return B(A(_mw,[_mz]));});return [1,_mD,_mC];}}},_mE=function(_mF,_mG,_mH,_mI,_){var _mJ=B(A(_mh,[_s,_6q,_mH,_mt,_])),_mK=_mJ,_mL=E(_mG),_mM=rMV(_mL),_mN=E(_mM),_mO=_mN[2],_mP=new T(function(){var _mQ=function(_mR){var _mS=E(_mR);return [0,_mS[1],_mS[2],_mK];},_mT=function(_mU){return new F(function(){return _6D(_mU,_mI);});};return B(_mu(_mT,_mQ,_mO));}),_=wMV(_mL,[0,_mN[1],_mP,_mN[3],_mN[4]]);return new F(function(){return A(_mF,[_]);});},_mV=function(_mW,_mX,_mY,_){var _mZ=rMV(_mX),_n0=_mZ,_n1=E(_mW),_n2=_n1,_n3=rMV(_n2),_n4=_n3,_n5=B(A(_jk,[_])),_n6=E(_n5);if(!_n6[0]){return new F(function(){return die(_jB);});}else{var _n7=_n6[1],_n8=B(A(_ji,[_])),_n9=E(_n8);if(!_n9[0]){return new F(function(){return die(_jy);});}else{var _na=_n9[1],_nb=jsFind(toJSStr(E(_jv)));if(!_nb[0]){return new F(function(){return die(_ju);});}else{var _nc=_nb[1],_nd=jsFind(toJSStr(E(_jr)));if(!_nd[0]){return new F(function(){return die(_jq);});}else{var _ne=new T(function(){return B(_iH(_n4));}),_nf=B(A(_jT,[_s,_6q,_nd[1],_j5,_ne,_])),_ng=E(_iX),_nh=jsFind(toJSStr(_ng));if(!_nh[0]){return new F(function(){return die(_jn);});}else{var _ni=_nh[1],_nj=E(_n4),_nk=function(_){var _nl=function(_nm,_){var _nn=rMV(_n2),_no=E(_nn),_np=_no[2],_nq=new T(function(){return B(_iz(_6D,_nm,_np));}),_=wMV(_n2,[0,_no[1],_nq,_no[3],_no[4]]);return new F(function(){return _mV(_n1,_mX,_mY,_);});},_nr=function(_){return new F(function(){return _mV(_n1,_mX,_mY,_);});},_ns=function(_nt,_nu,_){return new F(function(){return _mE(_nr,_n1,_nt,_nu,_);});},_nv=B(_cv(_ns,_nl,_nj,E(_nc),_)),_nw=E(_mY),_nx=rMV(_nw),_ny=_nx,_nz=E(_na),_nA=jsResetCanvas(_nz[2]),_nB=_nz[1],_nC=function(_nD,_){var _nE=jsDrawImage(E(_nD),E(_ny),0,0);return _9;},_nF=function(_nG,_){return new F(function(){return _dj(0.3,0.3,_nC,E(_nG),_);});},_nH=B(A(_gD,[_j1,_n0,_nF,_nB,_])),_nI=B(A(_jK,[_nj,_nB,_])),_nJ=rMV(_nw),_nK=E(_n7),_nL=_nK[1],_nM=jsResetCanvas(_nK[2]),_nN=jsPushState(_nL),_nO=jsScale(_nL,0.3,0.3),_nP=jsDrawImage(_nL,E(_nJ),0,0),_nQ=jsPopState(_nL),_nR=new T(function(){var _nS=function(_nu,_){return new F(function(){return _hJ(_n0,_nu,_);});},_nT=function(_nU,_){return new F(function(){return _ds(_nS,E(_nU),_);});};return B(_ii(_iY,_nT));}),_nV=B(A(_iK,[_iZ,_nR,_nL,_])),_nW=new T(function(){return B(_lm(_nj));},1),_nX=B(_fs(_ng,_nW,_)),_nY=new T(function(){var _nZ=new T(function(){return [4,E(B(_7F(_nj)))];}),_o0=new T(function(){return [4,E(B(_79(_n0)))];});return fromJSStr(B(_et([4,E(B(_7x(_6N,[1,_o0,[1,_nZ,_2W]])))])));},1);return new F(function(){return _fs(_iW,_nY,_);});};if(!B(_f6(_nj[2],_nj[3],_nj[4]))){var _o1=B(A(_fk,[_s,_6q,_ni,_j3,_j4,_]));return new F(function(){return _nk(_);});}else{var _o2=B(A(_fk,[_s,_6q,_ni,_j3,_j2,_]));return new F(function(){return _nk(_);});}}}}}}},_o3=function(_o4){return E(_o4)[2];},_o5=function(_){return _6h;},_o6=function(_o7,_){return new F(function(){return _o5(_);});},_o8=[0,_o3,_o6],_o9=function(_oa,_ob){while(1){var _oc=E(_oa);if(!_oc[0]){return E(_ob);}else{var _od=_oc[2],_oe=E(_oc[1]);if(_ob>_oe){_oa=_od;_ob=_oe;continue;}else{_oa=_od;continue;}}}},_of=function(_og,_oh,_oi){var _oj=E(_og);if(_oi>_oj){return new F(function(){return _o9(_oh,_oj);});}else{return new F(function(){return _o9(_oh,_oi);});}},_ok=2,_ol=4,_om=3,_on=function(_oo,_op){var _oq=function(_or,_os){while(1){var _ot=(function(_ou,_ov){var _ow=E(_ou);if(!_ow[0]){return [0];}else{var _ox=_ow[2];if(!B(A(_oo,[_ow[1]]))){_or=_ox;var _oy=_ov+1|0;_os=_oy;return null;}else{var _oz=new T(function(){return B(_oq(_ox,_ov+1|0));});return [1,_ov,_oz];}}})(_or,_os);if(_ot!=null){return _ot;}}},_oA=B(_oq(_op,0));return (_oA[0]==0)?[0]:[1,_oA[1]];},_oB=function(_oC){return E(_oC);},_oD=function(_oE,_oF,_oG,_){var _oH=function(_oI,_){var _oJ=E(_oE),_oK=rMV(_oJ),_oL=E(E(_oK)[2]),_oM=_oL[1],_oN=_oL[2],_oO=_oL[3],_oP=_oL[4],_oQ=new T(function(){var _oR=new T(function(){var _oS=E(E(_oI)[1]),_oT=_oS[1],_oU=_oS[2],_oV=new T(function(){return B(_oB(_oU));}),_oW=new T(function(){return B(_oB(_oT));});return [0,_oW,_oV];}),_oX=new T(function(){var _oY=E(_oR),_oZ=E(_oM);return Math.pow(E(_oY[1])-E(_oZ[1]),2)+Math.pow(E(_oY[2])-E(_oZ[2]),2);}),_p0=new T(function(){var _p1=E(_oR),_p2=E(_oN);return Math.pow(E(_p1[1])-E(_p2[1]),2)+Math.pow(E(_p1[2])-E(_p2[2]),2);}),_p3=new T(function(){var _p4=E(_oR),_p5=E(_oO);return Math.pow(E(_p4[1])-E(_p5[1]),2)+Math.pow(E(_p4[2])-E(_p5[2]),2);}),_p6=new T(function(){var _p7=E(_oR),_p8=E(_oP);return Math.pow(E(_p7[1])-E(_p8[1]),2)+Math.pow(E(_p7[2])-E(_p8[2]),2);}),_p9=[1,_p3,[1,_p6,_2W]],_pa=new T(function(){return B(_of(_p0,_p9,E(_oX)));}),_pb=function(_pc){return E(_pa)==E(_pc);},_pd=B(_on(_pb,[1,_oX,[1,_p0,_p9]]));if(!_pd[0]){return 3;}else{switch(E(_pd[1])){case 0:return 0;break;case 1:return 2;break;case 3:return 1;break;default:return 3;}}}),_=wMV(_oJ,[0,[1,_oQ],_oL]);return new F(function(){return A(_oG,[_]);});},_pe=B(A(_bS,[_6r,_o8,_9s,_oF,_ok,_oH,_])),_pf=function(_pg,_){var _ph=E(_oE),_pi=rMV(_ph),_=wMV(_ph,[0,_1x,E(_pi)[2]]);return new F(function(){return A(_oG,[_]);});},_pj=B(A(_bS,[_6r,_o8,_9s,_oF,_om,_pf,_])),_pk=function(_pl,_){var _pm=E(_oE),_pn=rMV(_pm),_po=E(_pn),_pp=_po[2],_pq=E(_po[1]);if(!_pq[0]){var _pr=E(_po);}else{var _ps=new T(function(){var _pt=E(E(_pl)[1]),_pu=_pt[1],_pv=_pt[2],_pw=new T(function(){return B(_oB(_pv));}),_px=new T(function(){return B(_oB(_pu));});return [0,_px,_pw];});switch(E(_pq[1])){case 0:var _py=E(_pp),_pz=[0,_pq,[0,_ps,_py[2],_py[3],_py[4]]];break;case 1:var _pA=E(_pp),_pz=[0,_pq,[0,_pA[1],_pA[2],_pA[3],_ps]];break;case 2:var _pB=E(_pp),_pz=[0,_pq,[0,_pB[1],_ps,_pB[3],_pB[4]]];break;default:var _pC=E(_pp),_pz=[0,_pq,[0,_pC[1],_pC[2],_ps,_pC[4]]];}var _pr=_pz;}var _=wMV(_pm,_pr);return new F(function(){return A(_oG,[_]);});},_pD=B(A(_bS,[_6r,_o8,_9s,_oF,_ol,_pk,_]));return _9;},_pE=new T(function(){return B(unCStr("Control.Exception.Base"));}),_pF=new T(function(){return B(unCStr("base"));}),_pG=new T(function(){return B(unCStr("PatternMatchFail"));}),_pH=new T(function(){var _pI=hs_wordToWord64(18445595),_pJ=hs_wordToWord64(52003073);return [0,_pI,_pJ,[0,_pI,_pJ,_pF,_pE,_pG],_2W,_2W];}),_pK=function(_pL){return E(_pH);},_pM=function(_pN){var _pO=E(_pN);return new F(function(){return _4B(B(_4z(_pO[1])),_pK,_pO[2]);});},_pP=function(_pQ){return E(E(_pQ)[1]);},_pR=function(_pS){return [0,_pT,_pS];},_pU=function(_pV,_pW){return new F(function(){return _G(E(_pV)[1],_pW);});},_pX=function(_pY,_pZ){return new F(function(){return _5T(_pU,_pY,_pZ);});},_q0=function(_q1,_q2,_q3){return new F(function(){return _G(E(_q2)[1],_q3);});},_q4=[0,_q0,_pP,_pX],_pT=new T(function(){return [0,_pK,_q4,_pR,_pM,_pP];}),_q5=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_q6=function(_q7){return E(E(_q7)[3]);},_q8=function(_q9,_qa){var _qb=new T(function(){return B(A(_q6,[_qa,_q9]));});return new F(function(){return die(_qb);});},_qc=function(_qd,_qe){return new F(function(){return _q8(_qd,_qe);});},_qf=function(_qg,_qh){var _qi=E(_qh);if(!_qi[0]){return [0,_2W,_2W];}else{var _qj=_qi[1],_qk=_qi[2];if(!B(A(_qg,[_qj]))){return [0,_2W,_qi];}else{var _ql=new T(function(){var _qm=B(_qf(_qg,_qk));return [0,_qm[1],_qm[2]];}),_qn=new T(function(){return E(E(_ql)[2]);}),_qo=new T(function(){return E(E(_ql)[1]);});return [0,[1,_qj,_qo],_qn];}}},_qp=32,_qq=new T(function(){return B(unCStr("\n"));}),_qr=function(_qs){return (E(_qs)==124)?false:true;},_qt=function(_qu,_qv){var _qw=B(_qf(_qr,B(unCStr(_qu)))),_qx=_qw[1],_qy=function(_qz,_qA){var _qB=new T(function(){var _qC=new T(function(){var _qD=new T(function(){return B(_G(_qA,_qq));},1);return B(_G(_qv,_qD));});return B(unAppCStr(": ",_qC));},1);return new F(function(){return _G(_qz,_qB);});},_qE=E(_qw[2]);if(!_qE[0]){return new F(function(){return _qy(_qx,_2W);});}else{if(E(_qE[1])==124){return new F(function(){return _qy(_qx,[1,_qp,_qE[2]]);});}else{return new F(function(){return _qy(_qx,_2W);});}}},_qF=function(_qG){var _qH=new T(function(){return B(_qt(_qG,_q5));});return new F(function(){return _qc([0,_qH],_pT);});},_qI=new T(function(){return B(_qF("Scans.hs:103:11-25|s : ss"));}),_qJ=function(_qK,_qL,_qM,_qN,_qO){if(!E(_qL)){return [0,_2t,_qM,_qN,_qO];}else{if(!B(_eO(_eN,_qM,_2W))){var _qP=new T(function(){var _qQ=E(_qM);if(!_qQ[0]){return E(_qI);}else{return [0,_qQ[1],_qQ[2]];}}),_qR=new T(function(){return E(E(_qP)[2]);}),_qS=new T(function(){return E(E(E(_qP)[1])[1]);}),_qT=new T(function(){var _qU=E(_qS),_qV=_qU[1],_qW=E(E(_qK)[1]),_qX=_qW[1],_qY=E(_qU[2]),_qZ=E(_qW[2]),_r0=_qZ-_qY;if(!_r0){var _r1=E(_qV),_r2=E(_qX),_r3=_r2-_r1;if(!_r3){return [0,_r2,_qY];}else{if(_r3<=0){if(0<= -_r3){return [0,_r2,_qY];}else{return [0,_r1,_qZ];}}else{if(0<=_r3){return [0,_r2,_qY];}else{return [0,_r1,_qZ];}}}}else{if(_r0<=0){var _r4=E(_qV),_r5=E(_qX),_r6=_r5-_r4;if(!_r6){if( -_r0<=0){return [0,_r5,_qY];}else{return [0,_r4,_qZ];}}else{if(_r6<=0){if( -_r0<= -_r6){return [0,_r5,_qY];}else{return [0,_r4,_qZ];}}else{if( -_r0<=_r6){return [0,_r5,_qY];}else{return [0,_r4,_qZ];}}}}else{var _r7=E(_qV),_r8=E(_qX),_r9=_r8-_r7;if(!_r9){return [0,_r7,_qZ];}else{if(_r9<=0){if(_r0<= -_r9){return [0,_r8,_qY];}else{return [0,_r7,_qZ];}}else{if(_r0<=_r9){return [0,_r8,_qY];}else{return [0,_r7,_qZ];}}}}}});return [0,_2r,[1,[0,_qS,_qT,_2W],_qR],_qN,_qO];}else{return [0,_2r,_qM,_qN,_qO];}}},_ra=function(_rb,_rc,_rd,_){var _re=function(_rf,_){var _rg=E(_rb),_rh=rMV(_rg),_ri=E(_rh),_rj=new T(function(){var _rk=E(E(_rf)[1]),_rl=_rk[1],_rm=_rk[2],_rn=new T(function(){return B(_oB(_rm));}),_ro=new T(function(){return B(_oB(_rl));});return [0,_ro,_rn];}),_=wMV(_rg,[0,_2r,[1,[0,_rj,_rj,_2W],_ri[2]],_ri[3],_ri[4]]);return new F(function(){return A(_rd,[_]);});},_rp=B(A(_bS,[_6r,_o8,_9s,_rc,_ok,_re,_])),_rq=function(_rr,_){var _rs=E(_rb),_rt=rMV(_rs),_ru=E(_rt),_rv=B(_qJ(_rr,_ru[1],_ru[2],_ru[3],_ru[4])),_=wMV(_rs,[0,_2t,_rv[2],_rv[3],_rv[4]]);return new F(function(){return A(_rd,[_]);});},_rw=B(A(_bS,[_6r,_o8,_9s,_rc,_om,_rq,_])),_rx=function(_ry,_){var _rz=E(_rb),_rA=rMV(_rz),_rB=E(_rA),_rC=B(_qJ(_ry,_rB[1],_rB[2],_rB[3],_rB[4])),_=wMV(_rz,[0,_rC[1],_rC[2],_rC[3],_rC[4]]);return new F(function(){return A(_rd,[_]);});},_rD=B(A(_bS,[_6r,_o8,_9s,_rc,_ol,_rx,_]));return _9;},_rE=(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);}),_rF=(function(x){return document.getElementById(x).value;}),_rG=0,_rH=[0,_rG,_rG],_rI=1191,_rJ=[0,_rI,_rG],_rK=669,_rL=[0,_rI,_rK],_rM=[0,_rG,_rK],_rN=[0,_rH,_rM,_rL,_rJ],_rO=[0,_1x,_rN],_rP=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:49:3-15"));}),_rQ=[0,_6h,_6i,_2W,_rP,_6h,_6h],_rR=new T(function(){return B(_6f(_rQ));}),_rS=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:50:3-15"));}),_rT=[0,_6h,_6i,_2W,_rS,_6h,_6h],_rU=new T(function(){return B(_6f(_rT));}),_rV=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:51:3-14"));}),_rW=[0,_6h,_6i,_2W,_rV,_6h,_6h],_rX=new T(function(){return B(_6f(_rW));}),_rY=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:52:3-11"));}),_rZ=[0,_6h,_6i,_2W,_rY,_6h,_6h],_s0=new T(function(){return B(_6f(_rZ));}),_s1=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:61:3-10"));}),_s2=[0,_6h,_6i,_2W,_s1,_6h,_6h],_s3=new T(function(){return B(_6f(_s2));}),_s4=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:62:3-11"));}),_s5=[0,_6h,_6i,_2W,_s4,_6h,_6h],_s6=new T(function(){return B(_6f(_s5));}),_s7=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:79:3-14"));}),_s8=[0,_6h,_6i,_2W,_s7,_6h,_6h],_s9=new T(function(){return B(_6f(_s8));}),_sa=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:80:3-11"));}),_sb=[0,_6h,_6i,_2W,_sa,_6h,_6h],_sc=new T(function(){return B(_6f(_sb));}),_sd=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_se=new T(function(){return B(err(_sd));}),_sf=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_sg=new T(function(){return B(err(_sf));}),_sh=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_si=function(_sj){var _sk=new T(function(){return B(_qt(_sj,_sh));});return new F(function(){return _qc([0,_sk],_pT);});},_sl=new T(function(){return B(_si("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_sm=function(_sn,_so){while(1){var _sp=(function(_sq,_sr){var _ss=E(_sq);switch(_ss[0]){case 0:var _st=E(_sr);if(!_st[0]){return [0];}else{_sn=B(A(_ss[1],[_st[1]]));_so=_st[2];return null;}break;case 1:var _su=B(A(_ss[1],[_sr])),_sv=_sr;_sn=_su;_so=_sv;return null;case 2:return [0];case 3:var _sw=_ss[2],_sx=new T(function(){return B(_sm(_sw,_sr));});return [1,[0,_ss[1],_sr],_sx];default:return E(_ss[1]);}})(_sn,_so);if(_sp!=null){return _sp;}}},_sy=function(_sz,_sA){var _sB=function(_sC){var _sD=E(_sA);if(_sD[0]==3){var _sE=_sD[2],_sF=new T(function(){return B(_sy(_sz,_sE));});return [3,_sD[1],_sF];}else{var _sG=E(_sz);if(_sG[0]==2){return E(_sD);}else{var _sH=E(_sD);if(_sH[0]==2){return E(_sG);}else{var _sI=function(_sJ){var _sK=E(_sH);if(_sK[0]==4){var _sL=_sK[1];return [1,function(_sM){return [4,new T(function(){return B(_G(B(_sm(_sG,_sM)),_sL));})];}];}else{var _sN=E(_sG);if(_sN[0]==1){var _sO=_sN[1],_sP=E(_sK);if(!_sP[0]){return [1,function(_sQ){return new F(function(){return _sy(B(A(_sO,[_sQ])),_sP);});}];}else{var _sR=_sP[1];return [1,function(_sS){var _sT=new T(function(){return B(A(_sR,[_sS]));});return new F(function(){return _sy(B(A(_sO,[_sS])),_sT);});}];}}else{var _sU=E(_sK);if(!_sU[0]){return E(_sl);}else{var _sV=_sU[1];return [1,function(_sW){var _sX=new T(function(){return B(A(_sV,[_sW]));});return new F(function(){return _sy(_sN,_sX);});}];}}}},_sY=E(_sG);switch(_sY[0]){case 1:var _sZ=_sY[1],_t0=E(_sH);if(_t0[0]==4){var _t1=_t0[1];return [1,function(_t2){return [4,new T(function(){return B(_G(B(_sm(B(A(_sZ,[_t2])),_t2)),_t1));})];}];}else{return new F(function(){return _sI(_);});}break;case 4:var _t3=_sY[1],_t4=E(_sH);switch(_t4[0]){case 0:return [1,function(_t5){return [4,new T(function(){var _t6=new T(function(){return B(_sm(_t4,_t5));},1);return B(_G(_t3,_t6));})];}];case 1:var _t7=_t4[1];return [1,function(_t8){return [4,new T(function(){var _t9=new T(function(){return B(_sm(B(A(_t7,[_t8])),_t8));},1);return B(_G(_t3,_t9));})];}];default:var _ta=_t4[1];return [4,new T(function(){return B(_G(_t3,_ta));})];}break;default:return new F(function(){return _sI(_);});}}}}},_tb=E(_sz);switch(_tb[0]){case 0:var _tc=_tb[1],_td=E(_sA);if(!_td[0]){var _te=_td[1];return [0,function(_tf){var _tg=new T(function(){return B(A(_te,[_tf]));});return new F(function(){return _sy(B(A(_tc,[_tf])),_tg);});}];}else{return new F(function(){return _sB(_);});}break;case 3:var _th=_tb[2],_ti=new T(function(){return B(_sy(_th,_sA));});return [3,_tb[1],_ti];default:return new F(function(){return _sB(_);});}},_tj=new T(function(){return B(unCStr("("));}),_tk=new T(function(){return B(unCStr(")"));}),_tl=function(_tm,_tn){return E(_tm)!=E(_tn);},_to=function(_tp,_tq){return E(_tp)==E(_tq);},_tr=[0,_to,_tl],_ts=function(_tt,_tu){while(1){var _tv=E(_tt);if(!_tv[0]){return (E(_tu)[0]==0)?true:false;}else{var _tw=E(_tu);if(!_tw[0]){return false;}else{if(E(_tv[1])!=E(_tw[1])){return false;}else{_tt=_tv[2];_tu=_tw[2];continue;}}}}},_tx=function(_ty,_tz){return (!B(_ts(_ty,_tz)))?true:false;},_tA=[0,_ts,_tx],_tB=function(_tC,_tD){var _tE=E(_tC);switch(_tE[0]){case 0:var _tF=_tE[1];return [0,function(_tG){return new F(function(){return _tB(B(A(_tF,[_tG])),_tD);});}];case 1:var _tH=_tE[1];return [1,function(_tI){return new F(function(){return _tB(B(A(_tH,[_tI])),_tD);});}];case 2:return [2];case 3:var _tJ=_tE[2],_tK=new T(function(){return B(_tB(_tJ,_tD));});return new F(function(){return _sy(B(A(_tD,[_tE[1]])),_tK);});break;default:var _tL=function(_tM){var _tN=E(_tM);if(!_tN[0]){return [0];}else{var _tO=_tN[2],_tP=E(_tN[1]),_tQ=new T(function(){return B(_tL(_tO));},1);return new F(function(){return _G(B(_sm(B(A(_tD,[_tP[1]])),_tP[2])),_tQ);});}},_tR=B(_tL(_tE[1]));return (_tR[0]==0)?[2]:[4,_tR];}},_tS=[2],_tT=function(_tU){return [3,_tU,_tS];},_tV=function(_tW,_tX){var _tY=E(_tW);if(!_tY){return new F(function(){return A(_tX,[_9]);});}else{var _tZ=new T(function(){return B(_tV(_tY-1|0,_tX));});return [0,function(_u0){return E(_tZ);}];}},_u1=function(_u2,_u3,_u4){var _u5=new T(function(){return B(A(_u2,[_tT]));}),_u6=function(_u7,_u8,_u9,_ua){while(1){var _ub=(function(_uc,_ud,_ue,_uf){var _ug=E(_uc);switch(_ug[0]){case 0:var _uh=E(_ud);if(!_uh[0]){return new F(function(){return A(_u3,[_uf]);});}else{_u7=B(A(_ug[1],[_uh[1]]));_u8=_uh[2];var _ui=_ue+1|0,_uj=_uf;_u9=_ui;_ua=_uj;return null;}break;case 1:var _uk=B(A(_ug[1],[_ud])),_ul=_ud,_ui=_ue,_uj=_uf;_u7=_uk;_u8=_ul;_u9=_ui;_ua=_uj;return null;case 2:return new F(function(){return A(_u3,[_uf]);});break;case 3:var _um=new T(function(){return B(_tB(_ug,_uf));}),_un=function(_uo){return E(_um);};return new F(function(){return _tV(_ue,_un);});break;default:return new F(function(){return _tB(_ug,_uf);});}})(_u7,_u8,_u9,_ua);if(_ub!=null){return _ub;}}};return function(_up){return new F(function(){return _u6(_u5,_up,0,_u4);});};},_uq=function(_ur){return new F(function(){return A(_ur,[_2W]);});},_us=function(_ut,_uu){var _uv=function(_uw){var _ux=E(_uw);if(!_ux[0]){return E(_uq);}else{var _uy=_ux[1],_uz=_ux[2];if(!B(A(_ut,[_uy]))){return E(_uq);}else{var _uA=new T(function(){return B(_uv(_uz));}),_uB=function(_uC){var _uD=new T(function(){var _uE=function(_uF){return new F(function(){return A(_uC,[[1,_uy,_uF]]);});};return B(A(_uA,[_uE]));});return [0,function(_uG){return E(_uD);}];};return E(_uB);}}};return function(_uH){return new F(function(){return A(_uv,[_uH,_uu]);});};},_uI=[6],_uJ=new T(function(){return B(unCStr("valDig: Bad base"));}),_uK=new T(function(){return B(err(_uJ));}),_uL=function(_uM,_uN){var _uO=function(_uP,_uQ){var _uR=E(_uP);if(!_uR[0]){var _uS=new T(function(){return B(A(_uQ,[_2W]));}),_uT=function(_uU){return new F(function(){return A(_uU,[_uS]);});};return E(_uT);}else{var _uV=_uR[2],_uW=E(_uR[1]),_uX=function(_uY){var _uZ=new T(function(){var _v0=function(_v1){return new F(function(){return A(_uQ,[[1,_uY,_v1]]);});};return B(_uO(_uV,_v0));}),_v2=function(_v3){var _v4=new T(function(){return B(A(_uZ,[_v3]));});return [0,function(_v5){return E(_v4);}];};return E(_v2);};switch(E(_uM)){case 8:if(48>_uW){var _v6=new T(function(){return B(A(_uQ,[_2W]));}),_v7=function(_v8){return new F(function(){return A(_v8,[_v6]);});};return E(_v7);}else{if(_uW>55){var _v9=new T(function(){return B(A(_uQ,[_2W]));}),_va=function(_vb){return new F(function(){return A(_vb,[_v9]);});};return E(_va);}else{return new F(function(){return _uX(_uW-48|0);});}}break;case 10:if(48>_uW){var _vc=new T(function(){return B(A(_uQ,[_2W]));}),_vd=function(_ve){return new F(function(){return A(_ve,[_vc]);});};return E(_vd);}else{if(_uW>57){var _vf=new T(function(){return B(A(_uQ,[_2W]));}),_vg=function(_vh){return new F(function(){return A(_vh,[_vf]);});};return E(_vg);}else{return new F(function(){return _uX(_uW-48|0);});}}break;case 16:if(48>_uW){if(97>_uW){if(65>_uW){var _vi=new T(function(){return B(A(_uQ,[_2W]));}),_vj=function(_vk){return new F(function(){return A(_vk,[_vi]);});};return E(_vj);}else{if(_uW>70){var _vl=new T(function(){return B(A(_uQ,[_2W]));}),_vm=function(_vn){return new F(function(){return A(_vn,[_vl]);});};return E(_vm);}else{return new F(function(){return _uX((_uW-65|0)+10|0);});}}}else{if(_uW>102){if(65>_uW){var _vo=new T(function(){return B(A(_uQ,[_2W]));}),_vp=function(_vq){return new F(function(){return A(_vq,[_vo]);});};return E(_vp);}else{if(_uW>70){var _vr=new T(function(){return B(A(_uQ,[_2W]));}),_vs=function(_vt){return new F(function(){return A(_vt,[_vr]);});};return E(_vs);}else{return new F(function(){return _uX((_uW-65|0)+10|0);});}}}else{return new F(function(){return _uX((_uW-97|0)+10|0);});}}}else{if(_uW>57){if(97>_uW){if(65>_uW){var _vu=new T(function(){return B(A(_uQ,[_2W]));}),_vv=function(_vw){return new F(function(){return A(_vw,[_vu]);});};return E(_vv);}else{if(_uW>70){var _vx=new T(function(){return B(A(_uQ,[_2W]));}),_vy=function(_vz){return new F(function(){return A(_vz,[_vx]);});};return E(_vy);}else{return new F(function(){return _uX((_uW-65|0)+10|0);});}}}else{if(_uW>102){if(65>_uW){var _vA=new T(function(){return B(A(_uQ,[_2W]));}),_vB=function(_vC){return new F(function(){return A(_vC,[_vA]);});};return E(_vB);}else{if(_uW>70){var _vD=new T(function(){return B(A(_uQ,[_2W]));}),_vE=function(_vF){return new F(function(){return A(_vF,[_vD]);});};return E(_vE);}else{return new F(function(){return _uX((_uW-65|0)+10|0);});}}}else{return new F(function(){return _uX((_uW-97|0)+10|0);});}}}else{return new F(function(){return _uX(_uW-48|0);});}}break;default:return E(_uK);}}},_vG=function(_vH){var _vI=E(_vH);if(!_vI[0]){return [2];}else{return new F(function(){return A(_uN,[_vI]);});}};return function(_vJ){return new F(function(){return A(_uO,[_vJ,_q,_vG]);});};},_vK=16,_vL=8,_vM=function(_vN){var _vO=function(_vP){return new F(function(){return A(_vN,[[5,[0,_vL,_vP]]]);});},_vQ=function(_vR){return new F(function(){return A(_vN,[[5,[0,_vK,_vR]]]);});},_vS=function(_vT){switch(E(_vT)){case 79:return [1,B(_uL(_vL,_vO))];case 88:return [1,B(_uL(_vK,_vQ))];case 111:return [1,B(_uL(_vL,_vO))];case 120:return [1,B(_uL(_vK,_vQ))];default:return [2];}},_vU=[0,_vS];return function(_vV){return (E(_vV)==48)?E(_vU):[2];};},_vW=function(_vX){return [0,B(_vM(_vX))];},_vY=function(_vZ){return new F(function(){return A(_vZ,[_6h]);});},_w0=function(_w1){return new F(function(){return A(_w1,[_6h]);});},_w2=10,_w3=[0,1],_w4=[0,2147483647],_w5=function(_w6,_w7){while(1){var _w8=E(_w6);if(!_w8[0]){var _w9=_w8[1],_wa=E(_w7);if(!_wa[0]){var _wb=_wa[1],_wc=addC(_w9,_wb);if(!E(_wc[2])){return [0,_wc[1]];}else{_w6=[1,I_fromInt(_w9)];_w7=[1,I_fromInt(_wb)];continue;}}else{_w6=[1,I_fromInt(_w9)];_w7=_wa;continue;}}else{var _wd=E(_w7);if(!_wd[0]){_w6=_w8;_w7=[1,I_fromInt(_wd[1])];continue;}else{return [1,I_add(_w8[1],_wd[1])];}}}},_we=new T(function(){return B(_w5(_w4,_w3));}),_wf=function(_wg){var _wh=E(_wg);if(!_wh[0]){var _wi=E(_wh[1]);return (_wi==(-2147483648))?E(_we):[0, -_wi];}else{return [1,I_negate(_wh[1])];}},_wj=[0,10],_wk=function(_wl,_wm){while(1){var _wn=E(_wl);if(!_wn[0]){return E(_wm);}else{_wl=_wn[2];var _wo=_wm+1|0;_wm=_wo;continue;}}},_wp=function(_wq){return new F(function(){return _l0(E(_wq));});},_wr=new T(function(){return B(unCStr("this should not happen"));}),_ws=new T(function(){return B(err(_wr));}),_wt=function(_wu,_wv){while(1){var _ww=E(_wu);if(!_ww[0]){var _wx=_ww[1],_wy=E(_wv);if(!_wy[0]){var _wz=_wy[1];if(!(imul(_wx,_wz)|0)){return [0,imul(_wx,_wz)|0];}else{_wu=[1,I_fromInt(_wx)];_wv=[1,I_fromInt(_wz)];continue;}}else{_wu=[1,I_fromInt(_wx)];_wv=_wy;continue;}}else{var _wA=E(_wv);if(!_wA[0]){_wu=_ww;_wv=[1,I_fromInt(_wA[1])];continue;}else{return [1,I_mul(_ww[1],_wA[1])];}}}},_wB=function(_wC,_wD){var _wE=E(_wD);if(!_wE[0]){return [0];}else{var _wF=E(_wE[2]);if(!_wF[0]){return E(_ws);}else{var _wG=_wF[2],_wH=new T(function(){return B(_wB(_wC,_wG));});return [1,B(_w5(B(_wt(_wE[1],_wC)),_wF[1])),_wH];}}},_wI=[0,0],_wJ=function(_wK,_wL,_wM){while(1){var _wN=(function(_wO,_wP,_wQ){var _wR=E(_wQ);if(!_wR[0]){return E(_wI);}else{if(!E(_wR[2])[0]){return E(_wR[1]);}else{var _wS=E(_wP);if(_wS<=40){var _wT=_wI,_wU=_wR;while(1){var _wV=E(_wU);if(!_wV[0]){return E(_wT);}else{var _wW=B(_w5(B(_wt(_wT,_wO)),_wV[1]));_wU=_wV[2];_wT=_wW;continue;}}}else{var _wX=B(_wt(_wO,_wO));if(!(_wS%2)){_wK=_wX;_wL=quot(_wS+1|0,2);var _wY=B(_wB(_wO,_wR));_wM=_wY;return null;}else{_wK=_wX;_wL=quot(_wS+1|0,2);var _wY=B(_wB(_wO,[1,_wI,_wR]));_wM=_wY;return null;}}}}})(_wK,_wL,_wM);if(_wN!=null){return _wN;}}},_wZ=function(_x0,_x1){var _x2=new T(function(){return B(_wk(_x1,0));},1);return new F(function(){return _wJ(_x0,_x2,B(_1d(_wp,_x1)));});},_x3=function(_x4){var _x5=new T(function(){var _x6=new T(function(){var _x7=function(_x8){var _x9=new T(function(){return B(_wZ(_wj,_x8));});return new F(function(){return A(_x4,[[1,_x9]]);});};return [1,B(_uL(_w2,_x7))];}),_xa=function(_xb){if(E(_xb)==43){var _xc=function(_xd){var _xe=new T(function(){return B(_wZ(_wj,_xd));});return new F(function(){return A(_x4,[[1,_xe]]);});};return [1,B(_uL(_w2,_xc))];}else{return [2];}},_xf=function(_xg){if(E(_xg)==45){var _xh=function(_xi){var _xj=new T(function(){return B(_wf(B(_wZ(_wj,_xi))));});return new F(function(){return A(_x4,[[1,_xj]]);});};return [1,B(_uL(_w2,_xh))];}else{return [2];}};return B(_sy(B(_sy([0,_xf],[0,_xa])),_x6));}),_xk=function(_xl){return (E(_xl)==69)?E(_x5):[2];},_xm=function(_xn){return (E(_xn)==101)?E(_x5):[2];};return new F(function(){return _sy([0,_xm],[0,_xk]);});},_xo=function(_xp){var _xq=function(_xr){return new F(function(){return A(_xp,[[1,_xr]]);});};return function(_xs){return (E(_xs)==46)?[1,B(_uL(_w2,_xq))]:[2];};},_xt=function(_xu){return [0,B(_xo(_xu))];},_xv=function(_xw){var _xx=function(_xy){var _xz=function(_xA){var _xB=function(_xC){return new F(function(){return A(_xw,[[5,[1,_xy,_xA,_xC]]]);});};return [1,B(_u1(_x3,_vY,_xB))];};return [1,B(_u1(_xt,_w0,_xz))];};return new F(function(){return _uL(_w2,_xx);});},_xD=function(_xE){return [1,B(_xv(_xE))];},_xF=function(_xG,_xH,_xI){while(1){var _xJ=E(_xI);if(!_xJ[0]){return false;}else{if(!B(A(_t,[_xG,_xH,_xJ[1]]))){_xI=_xJ[2];continue;}else{return true;}}}},_xK=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_xL=function(_xM){return new F(function(){return _xF(_tr,_xM,_xK);});},_xN=false,_xO=true,_xP=function(_xQ){var _xR=new T(function(){return B(A(_xQ,[_vL]));}),_xS=new T(function(){return B(A(_xQ,[_vK]));});return function(_xT){switch(E(_xT)){case 79:return E(_xR);case 88:return E(_xS);case 111:return E(_xR);case 120:return E(_xS);default:return [2];}};},_xU=function(_xV){return [0,B(_xP(_xV))];},_xW=function(_xX){return new F(function(){return A(_xX,[_w2]);});},_xY=function(_xZ){var _y0=new T(function(){return B(_7W(9,_xZ,_2W));});return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",_y0)));});},_y1=function(_y2){var _y3=E(_y2);if(!_y3[0]){return E(_y3[1]);}else{return new F(function(){return I_toInt(_y3[1]);});}},_y4=function(_y5,_y6){var _y7=E(_y5);if(!_y7[0]){var _y8=_y7[1],_y9=E(_y6);return (_y9[0]==0)?_y8<=_y9[1]:I_compareInt(_y9[1],_y8)>=0;}else{var _ya=_y7[1],_yb=E(_y6);return (_yb[0]==0)?I_compareInt(_ya,_yb[1])<=0:I_compare(_ya,_yb[1])<=0;}},_yc=function(_yd){return [2];},_ye=function(_yf){var _yg=E(_yf);if(!_yg[0]){return E(_yc);}else{var _yh=_yg[1],_yi=E(_yg[2]);if(!_yi[0]){return E(_yh);}else{var _yj=new T(function(){return B(_ye(_yi));}),_yk=function(_yl){var _ym=new T(function(){return B(A(_yj,[_yl]));});return new F(function(){return _sy(B(A(_yh,[_yl])),_ym);});};return E(_yk);}}},_yn=function(_yo,_yp){var _yq=function(_yr,_ys,_yt){var _yu=E(_yr);if(!_yu[0]){return new F(function(){return A(_yt,[_yo]);});}else{var _yv=_yu[2],_yw=E(_ys);if(!_yw[0]){return [2];}else{var _yx=_yw[2];if(E(_yu[1])!=E(_yw[1])){return [2];}else{var _yy=new T(function(){return B(_yq(_yv,_yx,_yt));});return [0,function(_yz){return E(_yy);}];}}}};return function(_yA){return new F(function(){return _yq(_yo,_yA,_yp);});};},_yB=new T(function(){return B(unCStr("SO"));}),_yC=14,_yD=function(_yE){var _yF=new T(function(){return B(A(_yE,[_yC]));}),_yG=function(_yH){return E(_yF);};return [1,B(_yn(_yB,_yG))];},_yI=new T(function(){return B(unCStr("SOH"));}),_yJ=1,_yK=function(_yL){var _yM=new T(function(){return B(A(_yL,[_yJ]));}),_yN=function(_yO){return E(_yM);};return [1,B(_yn(_yI,_yN))];},_yP=function(_yQ){return [1,B(_u1(_yK,_yD,_yQ))];},_yR=new T(function(){return B(unCStr("NUL"));}),_yS=0,_yT=function(_yU){var _yV=new T(function(){return B(A(_yU,[_yS]));}),_yW=function(_yX){return E(_yV);};return [1,B(_yn(_yR,_yW))];},_yY=new T(function(){return B(unCStr("STX"));}),_yZ=2,_z0=function(_z1){var _z2=new T(function(){return B(A(_z1,[_yZ]));}),_z3=function(_z4){return E(_z2);};return [1,B(_yn(_yY,_z3))];},_z5=new T(function(){return B(unCStr("ETX"));}),_z6=3,_z7=function(_z8){var _z9=new T(function(){return B(A(_z8,[_z6]));}),_za=function(_zb){return E(_z9);};return [1,B(_yn(_z5,_za))];},_zc=new T(function(){return B(unCStr("EOT"));}),_zd=4,_ze=function(_zf){var _zg=new T(function(){return B(A(_zf,[_zd]));}),_zh=function(_zi){return E(_zg);};return [1,B(_yn(_zc,_zh))];},_zj=new T(function(){return B(unCStr("ENQ"));}),_zk=5,_zl=function(_zm){var _zn=new T(function(){return B(A(_zm,[_zk]));}),_zo=function(_zp){return E(_zn);};return [1,B(_yn(_zj,_zo))];},_zq=new T(function(){return B(unCStr("ACK"));}),_zr=6,_zs=function(_zt){var _zu=new T(function(){return B(A(_zt,[_zr]));}),_zv=function(_zw){return E(_zu);};return [1,B(_yn(_zq,_zv))];},_zx=new T(function(){return B(unCStr("BEL"));}),_zy=7,_zz=function(_zA){var _zB=new T(function(){return B(A(_zA,[_zy]));}),_zC=function(_zD){return E(_zB);};return [1,B(_yn(_zx,_zC))];},_zE=new T(function(){return B(unCStr("BS"));}),_zF=8,_zG=function(_zH){var _zI=new T(function(){return B(A(_zH,[_zF]));}),_zJ=function(_zK){return E(_zI);};return [1,B(_yn(_zE,_zJ))];},_zL=new T(function(){return B(unCStr("HT"));}),_zM=9,_zN=function(_zO){var _zP=new T(function(){return B(A(_zO,[_zM]));}),_zQ=function(_zR){return E(_zP);};return [1,B(_yn(_zL,_zQ))];},_zS=new T(function(){return B(unCStr("LF"));}),_zT=10,_zU=function(_zV){var _zW=new T(function(){return B(A(_zV,[_zT]));}),_zX=function(_zY){return E(_zW);};return [1,B(_yn(_zS,_zX))];},_zZ=new T(function(){return B(unCStr("VT"));}),_A0=11,_A1=function(_A2){var _A3=new T(function(){return B(A(_A2,[_A0]));}),_A4=function(_A5){return E(_A3);};return [1,B(_yn(_zZ,_A4))];},_A6=new T(function(){return B(unCStr("FF"));}),_A7=12,_A8=function(_A9){var _Aa=new T(function(){return B(A(_A9,[_A7]));}),_Ab=function(_Ac){return E(_Aa);};return [1,B(_yn(_A6,_Ab))];},_Ad=new T(function(){return B(unCStr("CR"));}),_Ae=13,_Af=function(_Ag){var _Ah=new T(function(){return B(A(_Ag,[_Ae]));}),_Ai=function(_Aj){return E(_Ah);};return [1,B(_yn(_Ad,_Ai))];},_Ak=new T(function(){return B(unCStr("SI"));}),_Al=15,_Am=function(_An){var _Ao=new T(function(){return B(A(_An,[_Al]));}),_Ap=function(_Aq){return E(_Ao);};return [1,B(_yn(_Ak,_Ap))];},_Ar=new T(function(){return B(unCStr("DLE"));}),_As=16,_At=function(_Au){var _Av=new T(function(){return B(A(_Au,[_As]));}),_Aw=function(_Ax){return E(_Av);};return [1,B(_yn(_Ar,_Aw))];},_Ay=new T(function(){return B(unCStr("DC1"));}),_Az=17,_AA=function(_AB){var _AC=new T(function(){return B(A(_AB,[_Az]));}),_AD=function(_AE){return E(_AC);};return [1,B(_yn(_Ay,_AD))];},_AF=new T(function(){return B(unCStr("DC2"));}),_AG=18,_AH=function(_AI){var _AJ=new T(function(){return B(A(_AI,[_AG]));}),_AK=function(_AL){return E(_AJ);};return [1,B(_yn(_AF,_AK))];},_AM=new T(function(){return B(unCStr("DC3"));}),_AN=19,_AO=function(_AP){var _AQ=new T(function(){return B(A(_AP,[_AN]));}),_AR=function(_AS){return E(_AQ);};return [1,B(_yn(_AM,_AR))];},_AT=new T(function(){return B(unCStr("DC4"));}),_AU=20,_AV=function(_AW){var _AX=new T(function(){return B(A(_AW,[_AU]));}),_AY=function(_AZ){return E(_AX);};return [1,B(_yn(_AT,_AY))];},_B0=new T(function(){return B(unCStr("NAK"));}),_B1=21,_B2=function(_B3){var _B4=new T(function(){return B(A(_B3,[_B1]));}),_B5=function(_B6){return E(_B4);};return [1,B(_yn(_B0,_B5))];},_B7=new T(function(){return B(unCStr("SYN"));}),_B8=22,_B9=function(_Ba){var _Bb=new T(function(){return B(A(_Ba,[_B8]));}),_Bc=function(_Bd){return E(_Bb);};return [1,B(_yn(_B7,_Bc))];},_Be=new T(function(){return B(unCStr("ETB"));}),_Bf=23,_Bg=function(_Bh){var _Bi=new T(function(){return B(A(_Bh,[_Bf]));}),_Bj=function(_Bk){return E(_Bi);};return [1,B(_yn(_Be,_Bj))];},_Bl=new T(function(){return B(unCStr("CAN"));}),_Bm=24,_Bn=function(_Bo){var _Bp=new T(function(){return B(A(_Bo,[_Bm]));}),_Bq=function(_Br){return E(_Bp);};return [1,B(_yn(_Bl,_Bq))];},_Bs=new T(function(){return B(unCStr("EM"));}),_Bt=25,_Bu=function(_Bv){var _Bw=new T(function(){return B(A(_Bv,[_Bt]));}),_Bx=function(_By){return E(_Bw);};return [1,B(_yn(_Bs,_Bx))];},_Bz=new T(function(){return B(unCStr("SUB"));}),_BA=26,_BB=function(_BC){var _BD=new T(function(){return B(A(_BC,[_BA]));}),_BE=function(_BF){return E(_BD);};return [1,B(_yn(_Bz,_BE))];},_BG=new T(function(){return B(unCStr("ESC"));}),_BH=27,_BI=function(_BJ){var _BK=new T(function(){return B(A(_BJ,[_BH]));}),_BL=function(_BM){return E(_BK);};return [1,B(_yn(_BG,_BL))];},_BN=new T(function(){return B(unCStr("FS"));}),_BO=28,_BP=function(_BQ){var _BR=new T(function(){return B(A(_BQ,[_BO]));}),_BS=function(_BT){return E(_BR);};return [1,B(_yn(_BN,_BS))];},_BU=new T(function(){return B(unCStr("GS"));}),_BV=29,_BW=function(_BX){var _BY=new T(function(){return B(A(_BX,[_BV]));}),_BZ=function(_C0){return E(_BY);};return [1,B(_yn(_BU,_BZ))];},_C1=new T(function(){return B(unCStr("RS"));}),_C2=30,_C3=function(_C4){var _C5=new T(function(){return B(A(_C4,[_C2]));}),_C6=function(_C7){return E(_C5);};return [1,B(_yn(_C1,_C6))];},_C8=new T(function(){return B(unCStr("US"));}),_C9=31,_Ca=function(_Cb){var _Cc=new T(function(){return B(A(_Cb,[_C9]));}),_Cd=function(_Ce){return E(_Cc);};return [1,B(_yn(_C8,_Cd))];},_Cf=new T(function(){return B(unCStr("SP"));}),_Cg=32,_Ch=function(_Ci){var _Cj=new T(function(){return B(A(_Ci,[_Cg]));}),_Ck=function(_Cl){return E(_Cj);};return [1,B(_yn(_Cf,_Ck))];},_Cm=new T(function(){return B(unCStr("DEL"));}),_Cn=127,_Co=function(_Cp){var _Cq=new T(function(){return B(A(_Cp,[_Cn]));}),_Cr=function(_Cs){return E(_Cq);};return [1,B(_yn(_Cm,_Cr))];},_Ct=[1,_Co,_2W],_Cu=[1,_Ch,_Ct],_Cv=[1,_Ca,_Cu],_Cw=[1,_C3,_Cv],_Cx=[1,_BW,_Cw],_Cy=[1,_BP,_Cx],_Cz=[1,_BI,_Cy],_CA=[1,_BB,_Cz],_CB=[1,_Bu,_CA],_CC=[1,_Bn,_CB],_CD=[1,_Bg,_CC],_CE=[1,_B9,_CD],_CF=[1,_B2,_CE],_CG=[1,_AV,_CF],_CH=[1,_AO,_CG],_CI=[1,_AH,_CH],_CJ=[1,_AA,_CI],_CK=[1,_At,_CJ],_CL=[1,_Am,_CK],_CM=[1,_Af,_CL],_CN=[1,_A8,_CM],_CO=[1,_A1,_CN],_CP=[1,_zU,_CO],_CQ=[1,_zN,_CP],_CR=[1,_zG,_CQ],_CS=[1,_zz,_CR],_CT=[1,_zs,_CS],_CU=[1,_zl,_CT],_CV=[1,_ze,_CU],_CW=[1,_z7,_CV],_CX=[1,_z0,_CW],_CY=[1,_yT,_CX],_CZ=[1,_yP,_CY],_D0=new T(function(){return B(_ye(_CZ));}),_D1=34,_D2=[0,1114111],_D3=92,_D4=39,_D5=function(_D6){var _D7=new T(function(){return B(A(_D6,[_zy]));}),_D8=new T(function(){return B(A(_D6,[_zF]));}),_D9=new T(function(){return B(A(_D6,[_zM]));}),_Da=new T(function(){return B(A(_D6,[_zT]));}),_Db=new T(function(){return B(A(_D6,[_A0]));}),_Dc=new T(function(){return B(A(_D6,[_A7]));}),_Dd=new T(function(){return B(A(_D6,[_Ae]));}),_De=new T(function(){return B(A(_D6,[_D3]));}),_Df=new T(function(){return B(A(_D6,[_D4]));}),_Dg=new T(function(){return B(A(_D6,[_D1]));}),_Dh=new T(function(){var _Di=function(_Dj){var _Dk=new T(function(){return B(_l0(E(_Dj)));}),_Dl=function(_Dm){var _Dn=B(_wZ(_Dk,_Dm));if(!B(_y4(_Dn,_D2))){return [2];}else{var _Do=new T(function(){var _Dp=B(_y1(_Dn));if(_Dp>>>0>1114111){return B(_xY(_Dp));}else{return _Dp;}});return new F(function(){return A(_D6,[_Do]);});}};return [1,B(_uL(_Dj,_Dl))];},_Dq=new T(function(){var _Dr=new T(function(){return B(A(_D6,[_C9]));}),_Ds=new T(function(){return B(A(_D6,[_C2]));}),_Dt=new T(function(){return B(A(_D6,[_BV]));}),_Du=new T(function(){return B(A(_D6,[_BO]));}),_Dv=new T(function(){return B(A(_D6,[_BH]));}),_Dw=new T(function(){return B(A(_D6,[_BA]));}),_Dx=new T(function(){return B(A(_D6,[_Bt]));}),_Dy=new T(function(){return B(A(_D6,[_Bm]));}),_Dz=new T(function(){return B(A(_D6,[_Bf]));}),_DA=new T(function(){return B(A(_D6,[_B8]));}),_DB=new T(function(){return B(A(_D6,[_B1]));}),_DC=new T(function(){return B(A(_D6,[_AU]));}),_DD=new T(function(){return B(A(_D6,[_AN]));}),_DE=new T(function(){return B(A(_D6,[_AG]));}),_DF=new T(function(){return B(A(_D6,[_Az]));}),_DG=new T(function(){return B(A(_D6,[_As]));}),_DH=new T(function(){return B(A(_D6,[_Al]));}),_DI=new T(function(){return B(A(_D6,[_yC]));}),_DJ=new T(function(){return B(A(_D6,[_zr]));}),_DK=new T(function(){return B(A(_D6,[_zk]));}),_DL=new T(function(){return B(A(_D6,[_zd]));}),_DM=new T(function(){return B(A(_D6,[_z6]));}),_DN=new T(function(){return B(A(_D6,[_yZ]));}),_DO=new T(function(){return B(A(_D6,[_yJ]));}),_DP=new T(function(){return B(A(_D6,[_yS]));}),_DQ=function(_DR){switch(E(_DR)){case 64:return E(_DP);case 65:return E(_DO);case 66:return E(_DN);case 67:return E(_DM);case 68:return E(_DL);case 69:return E(_DK);case 70:return E(_DJ);case 71:return E(_D7);case 72:return E(_D8);case 73:return E(_D9);case 74:return E(_Da);case 75:return E(_Db);case 76:return E(_Dc);case 77:return E(_Dd);case 78:return E(_DI);case 79:return E(_DH);case 80:return E(_DG);case 81:return E(_DF);case 82:return E(_DE);case 83:return E(_DD);case 84:return E(_DC);case 85:return E(_DB);case 86:return E(_DA);case 87:return E(_Dz);case 88:return E(_Dy);case 89:return E(_Dx);case 90:return E(_Dw);case 91:return E(_Dv);case 92:return E(_Du);case 93:return E(_Dt);case 94:return E(_Ds);case 95:return E(_Dr);default:return [2];}},_DS=[0,_DQ],_DT=new T(function(){return B(A(_D0,[_D6]));}),_DU=function(_DV){return (E(_DV)==94)?E(_DS):[2];};return B(_sy([0,_DU],_DT));});return B(_sy([1,B(_u1(_xU,_xW,_Di))],_Dq));}),_DW=function(_DX){switch(E(_DX)){case 34:return E(_Dg);case 39:return E(_Df);case 92:return E(_De);case 97:return E(_D7);case 98:return E(_D8);case 102:return E(_Dc);case 110:return E(_Da);case 114:return E(_Dd);case 116:return E(_D9);case 118:return E(_Db);default:return [2];}};return new F(function(){return _sy([0,_DW],_Dh);});},_DY=function(_DZ){return new F(function(){return A(_DZ,[_9]);});},_E0=function(_E1){var _E2=E(_E1);if(!_E2[0]){return E(_DY);}else{var _E3=_E2[2],_E4=E(_E2[1]),_E5=_E4>>>0,_E6=new T(function(){return B(_E0(_E3));});if(_E5>887){var _E7=u_iswspace(_E4);if(!E(_E7)){return E(_DY);}else{var _E8=function(_E9){var _Ea=new T(function(){return B(A(_E6,[_E9]));});return [0,function(_Eb){return E(_Ea);}];};return E(_E8);}}else{var _Ec=E(_E5);if(_Ec==32){var _Ed=function(_Ee){var _Ef=new T(function(){return B(A(_E6,[_Ee]));});return [0,function(_Eg){return E(_Ef);}];};return E(_Ed);}else{if(_Ec-9>>>0>4){if(E(_Ec)==160){var _Eh=function(_Ei){var _Ej=new T(function(){return B(A(_E6,[_Ei]));});return [0,function(_Ek){return E(_Ej);}];};return E(_Eh);}else{return E(_DY);}}else{var _El=function(_Em){var _En=new T(function(){return B(A(_E6,[_Em]));});return [0,function(_Eo){return E(_En);}];};return E(_El);}}}}},_Ep=function(_Eq){var _Er=new T(function(){return B(_Ep(_Eq));}),_Es=function(_Et){return (E(_Et)==92)?E(_Er):[2];},_Eu=[0,_Es],_Ev=function(_Ew){return E(_Eu);},_Ex=function(_Ey){return new F(function(){return A(_E0,[_Ey,_Ev]);});},_Ez=[1,_Ex],_EA=new T(function(){var _EB=function(_EC){return new F(function(){return A(_Eq,[[0,_EC,_xO]]);});};return B(_D5(_EB));}),_ED=function(_EE){var _EF=E(_EE);if(_EF==38){return E(_Er);}else{var _EG=_EF>>>0;if(_EG>887){var _EH=u_iswspace(_EF);return (E(_EH)==0)?[2]:E(_Ez);}else{var _EI=E(_EG);return (_EI==32)?E(_Ez):(_EI-9>>>0>4)?(E(_EI)==160)?E(_Ez):[2]:E(_Ez);}}},_EJ=[0,_ED],_EK=function(_EL){var _EM=E(_EL);if(E(_EM)==92){return E(_EA);}else{return new F(function(){return A(_Eq,[[0,_EM,_xN]]);});}},_EN=function(_EO){return (E(_EO)==92)?E(_EJ):[2];};return new F(function(){return _sy([0,_EN],[0,_EK]);});},_EP=function(_EQ,_ER){var _ES=new T(function(){var _ET=new T(function(){return B(A(_EQ,[_2W]));});return B(A(_ER,[[1,_ET]]));}),_EU=function(_EV){var _EW=E(_EV),_EX=E(_EW[1]);if(E(_EX)==34){if(!E(_EW[2])){return E(_ES);}else{var _EY=function(_EZ){return new F(function(){return A(_EQ,[[1,_EX,_EZ]]);});};return new F(function(){return _EP(_EY,_ER);});}}else{var _F0=function(_F1){return new F(function(){return A(_EQ,[[1,_EX,_F1]]);});};return new F(function(){return _EP(_F0,_ER);});}};return new F(function(){return _Ep(_EU);});},_F2=new T(function(){return B(unCStr("_\'"));}),_F3=function(_F4){var _F5=u_iswalnum(_F4);if(!E(_F5)){return new F(function(){return _xF(_tr,_F4,_F2);});}else{return true;}},_F6=function(_F7){return new F(function(){return _F3(E(_F7));});},_F8=new T(function(){return B(unCStr(",;()[]{}`"));}),_F9=new T(function(){return B(unCStr("=>"));}),_Fa=[1,_F9,_2W],_Fb=new T(function(){return B(unCStr("~"));}),_Fc=[1,_Fb,_Fa],_Fd=new T(function(){return B(unCStr("@"));}),_Fe=[1,_Fd,_Fc],_Ff=new T(function(){return B(unCStr("->"));}),_Fg=[1,_Ff,_Fe],_Fh=new T(function(){return B(unCStr("<-"));}),_Fi=[1,_Fh,_Fg],_Fj=new T(function(){return B(unCStr("|"));}),_Fk=[1,_Fj,_Fi],_Fl=new T(function(){return B(unCStr("\\"));}),_Fm=[1,_Fl,_Fk],_Fn=new T(function(){return B(unCStr("="));}),_Fo=[1,_Fn,_Fm],_Fp=new T(function(){return B(unCStr("::"));}),_Fq=[1,_Fp,_Fo],_Fr=new T(function(){return B(unCStr(".."));}),_Fs=[1,_Fr,_Fq],_Ft=function(_Fu){var _Fv=new T(function(){return B(A(_Fu,[_uI]));}),_Fw=new T(function(){var _Fx=new T(function(){var _Fy=function(_Fz){var _FA=new T(function(){return B(A(_Fu,[[0,_Fz]]));});return [0,function(_FB){return (E(_FB)==39)?E(_FA):[2];}];};return B(_D5(_Fy));}),_FC=function(_FD){var _FE=E(_FD);switch(E(_FE)){case 39:return [2];case 92:return E(_Fx);default:var _FF=new T(function(){return B(A(_Fu,[[0,_FE]]));});return [0,function(_FG){return (E(_FG)==39)?E(_FF):[2];}];}},_FH=[0,_FC],_FI=new T(function(){var _FJ=new T(function(){return B(_EP(_q,_Fu));}),_FK=new T(function(){var _FL=new T(function(){var _FM=new T(function(){var _FN=new T(function(){return [1,B(_u1(_vW,_xD,_Fu))];}),_FO=function(_FP){var _FQ=E(_FP),_FR=u_iswalpha(_FQ);if(!E(_FR)){if(E(_FQ)==95){var _FS=function(_FT){return new F(function(){return A(_Fu,[[3,[1,_FQ,_FT]]]);});};return [1,B(_us(_F6,_FS))];}else{return [2];}}else{var _FU=function(_FV){return new F(function(){return A(_Fu,[[3,[1,_FQ,_FV]]]);});};return [1,B(_us(_F6,_FU))];}};return B(_sy([0,_FO],_FN));}),_FW=function(_FX){if(!B(_xF(_tr,_FX,_xK))){return [2];}else{var _FY=function(_FZ){var _G0=[1,_FX,_FZ];if(!B(_xF(_tA,_G0,_Fs))){return new F(function(){return A(_Fu,[[4,_G0]]);});}else{return new F(function(){return A(_Fu,[[2,_G0]]);});}};return [1,B(_us(_xL,_FY))];}};return B(_sy([0,_FW],_FM));}),_G1=function(_G2){if(!B(_xF(_tr,_G2,_F8))){return [2];}else{return new F(function(){return A(_Fu,[[2,[1,_G2,_2W]]]);});}};return B(_sy([0,_G1],_FL));}),_G3=function(_G4){return (E(_G4)==34)?E(_FJ):[2];};return B(_sy([0,_G3],_FK));}),_G5=function(_G6){return (E(_G6)==39)?E(_FH):[2];};return B(_sy([0,_G5],_FI));}),_G7=function(_G8){return (E(_G8)[0]==0)?E(_Fv):[2];};return new F(function(){return _sy([1,_G7],_Fw);});},_G9=0,_Ga=function(_Gb,_Gc){var _Gd=new T(function(){var _Ge=new T(function(){var _Gf=function(_Gg){var _Gh=new T(function(){var _Gi=new T(function(){return B(A(_Gc,[_Gg]));}),_Gj=function(_Gk){var _Gl=E(_Gk);return (_Gl[0]==2)?(!B(_1N(_Gl[1],_tk)))?[2]:E(_Gi):[2];};return B(_Ft(_Gj));}),_Gm=function(_Gn){return E(_Gh);};return [1,function(_Go){return new F(function(){return A(_E0,[_Go,_Gm]);});}];};return B(A(_Gb,[_G9,_Gf]));}),_Gp=function(_Gq){var _Gr=E(_Gq);return (_Gr[0]==2)?(!B(_1N(_Gr[1],_tj)))?[2]:E(_Ge):[2];};return B(_Ft(_Gp));}),_Gs=function(_Gt){return E(_Gd);};return function(_Gu){return new F(function(){return A(_E0,[_Gu,_Gs]);});};},_Gv=function(_Gw,_Gx){var _Gy=function(_Gz){var _GA=new T(function(){return B(A(_Gw,[_Gz]));}),_GB=function(_GC){var _GD=new T(function(){return [1,B(_Ga(_Gy,_GC))];});return new F(function(){return _sy(B(A(_GA,[_GC])),_GD);});};return E(_GB);},_GE=new T(function(){return B(A(_Gw,[_Gx]));}),_GF=function(_GG){var _GH=new T(function(){return [1,B(_Ga(_Gy,_GG))];});return new F(function(){return _sy(B(A(_GE,[_GG])),_GH);});};return E(_GF);},_GI=function(_GJ,_GK){var _GL=function(_GM,_GN){var _GO=function(_GP){var _GQ=new T(function(){return  -E(_GP);});return new F(function(){return A(_GN,[_GQ]);});},_GR=function(_GS){return new F(function(){return A(_GJ,[_GS,_GM,_GO]);});},_GT=new T(function(){return B(_Ft(_GR));}),_GU=function(_GV){return E(_GT);},_GW=function(_GX){return new F(function(){return A(_E0,[_GX,_GU]);});},_GY=[1,_GW],_GZ=function(_H0){var _H1=E(_H0);if(_H1[0]==4){var _H2=E(_H1[1]);if(!_H2[0]){return new F(function(){return A(_GJ,[_H1,_GM,_GN]);});}else{if(E(_H2[1])==45){if(!E(_H2[2])[0]){return E(_GY);}else{return new F(function(){return A(_GJ,[_H1,_GM,_GN]);});}}else{return new F(function(){return A(_GJ,[_H1,_GM,_GN]);});}}}else{return new F(function(){return A(_GJ,[_H1,_GM,_GN]);});}},_H3=new T(function(){return B(_Ft(_GZ));}),_H4=function(_H5){return E(_H3);};return [1,function(_H6){return new F(function(){return A(_E0,[_H6,_H4]);});}];};return new F(function(){return _Gv(_GL,_GK);});},_H7=new T(function(){return 1/0;}),_H8=function(_H9,_Ha){return new F(function(){return A(_Ha,[_H7]);});},_Hb=new T(function(){return 0/0;}),_Hc=function(_Hd,_He){return new F(function(){return A(_He,[_Hb]);});},_Hf=new T(function(){return B(unCStr("NaN"));}),_Hg=new T(function(){return B(unCStr("Infinity"));}),_Hh=1024,_Hi=-1021,_Hj=new T(function(){return B(unCStr("GHC.Exception"));}),_Hk=new T(function(){return B(unCStr("base"));}),_Hl=new T(function(){return B(unCStr("ArithException"));}),_Hm=new T(function(){var _Hn=hs_wordToWord64(4194982440),_Ho=hs_wordToWord64(3110813675);return [0,_Hn,_Ho,[0,_Hn,_Ho,_Hk,_Hj,_Hl],_2W,_2W];}),_Hp=function(_Hq){return E(_Hm);},_Hr=function(_Hs){var _Ht=E(_Hs);return new F(function(){return _4B(B(_4z(_Ht[1])),_Hp,_Ht[2]);});},_Hu=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_Hv=new T(function(){return B(unCStr("denormal"));}),_Hw=new T(function(){return B(unCStr("divide by zero"));}),_Hx=new T(function(){return B(unCStr("loss of precision"));}),_Hy=new T(function(){return B(unCStr("arithmetic underflow"));}),_Hz=new T(function(){return B(unCStr("arithmetic overflow"));}),_HA=function(_HB,_HC){switch(E(_HB)){case 0:return new F(function(){return _G(_Hz,_HC);});break;case 1:return new F(function(){return _G(_Hy,_HC);});break;case 2:return new F(function(){return _G(_Hx,_HC);});break;case 3:return new F(function(){return _G(_Hw,_HC);});break;case 4:return new F(function(){return _G(_Hv,_HC);});break;default:return new F(function(){return _G(_Hu,_HC);});}},_HD=function(_HE){return new F(function(){return _HA(_HE,_2W);});},_HF=function(_HG,_HH,_HI){return new F(function(){return _HA(_HH,_HI);});},_HJ=function(_HK,_HL){return new F(function(){return _5T(_HA,_HK,_HL);});},_HM=[0,_HF,_HD,_HJ],_HN=new T(function(){return [0,_Hp,_HM,_HO,_Hr,_HD];}),_HO=function(_qe){return [0,_HN,_qe];},_HP=3,_HQ=new T(function(){return B(_HO(_HP));}),_HR=new T(function(){return die(_HQ);}),_HS=function(_HT,_HU){var _HV=E(_HT);if(!_HV[0]){var _HW=_HV[1],_HX=E(_HU);return (_HX[0]==0)?_HW==_HX[1]:(I_compareInt(_HX[1],_HW)==0)?true:false;}else{var _HY=_HV[1],_HZ=E(_HU);return (_HZ[0]==0)?(I_compareInt(_HY,_HZ[1])==0)?true:false:(I_compare(_HY,_HZ[1])==0)?true:false;}},_I0=[0,0],_I1=function(_I2,_I3){while(1){var _I4=E(_I2);if(!_I4[0]){var _I5=E(_I4[1]);if(_I5==(-2147483648)){_I2=[1,I_fromInt(-2147483648)];continue;}else{var _I6=E(_I3);if(!_I6[0]){return [0,_I5%_I6[1]];}else{_I2=[1,I_fromInt(_I5)];_I3=_I6;continue;}}}else{var _I7=_I4[1],_I8=E(_I3);return (_I8[0]==0)?[1,I_rem(_I7,I_fromInt(_I8[1]))]:[1,I_rem(_I7,_I8[1])];}}},_I9=function(_Ia,_Ib){if(!B(_HS(_Ib,_I0))){return new F(function(){return _I1(_Ia,_Ib);});}else{return E(_HR);}},_Ic=function(_Id,_Ie){while(1){if(!B(_HS(_Ie,_I0))){var _If=_Ie,_Ig=B(_I9(_Id,_Ie));_Id=_If;_Ie=_Ig;continue;}else{return E(_Id);}}},_Ih=function(_Ii){var _Ij=E(_Ii);if(!_Ij[0]){var _Ik=E(_Ij[1]);return (_Ik==(-2147483648))?E(_we):(_Ik<0)?[0, -_Ik]:E(_Ij);}else{var _Il=_Ij[1];return (I_compareInt(_Il,0)>=0)?E(_Ij):[1,I_negate(_Il)];}},_Im=function(_In,_Io){while(1){var _Ip=E(_In);if(!_Ip[0]){var _Iq=E(_Ip[1]);if(_Iq==(-2147483648)){_In=[1,I_fromInt(-2147483648)];continue;}else{var _Ir=E(_Io);if(!_Ir[0]){return [0,quot(_Iq,_Ir[1])];}else{_In=[1,I_fromInt(_Iq)];_Io=_Ir;continue;}}}else{var _Is=_Ip[1],_It=E(_Io);return (_It[0]==0)?[0,I_toInt(I_quot(_Is,I_fromInt(_It[1])))]:[1,I_quot(_Is,_It[1])];}}},_Iu=5,_Iv=new T(function(){return B(_HO(_Iu));}),_Iw=new T(function(){return die(_Iv);}),_Ix=function(_Iy,_Iz){if(!B(_HS(_Iz,_I0))){var _IA=B(_Ic(B(_Ih(_Iy)),B(_Ih(_Iz))));return (!B(_HS(_IA,_I0)))?[0,B(_Im(_Iy,_IA)),B(_Im(_Iz,_IA))]:E(_HR);}else{return E(_Iw);}},_IB=[0,1],_IC=new T(function(){return B(unCStr("Negative exponent"));}),_ID=new T(function(){return B(err(_IC));}),_IE=[0,2],_IF=new T(function(){return B(_HS(_IE,_I0));}),_IG=function(_IH,_II){while(1){var _IJ=E(_IH);if(!_IJ[0]){var _IK=_IJ[1],_IL=E(_II);if(!_IL[0]){var _IM=_IL[1],_IN=subC(_IK,_IM);if(!E(_IN[2])){return [0,_IN[1]];}else{_IH=[1,I_fromInt(_IK)];_II=[1,I_fromInt(_IM)];continue;}}else{_IH=[1,I_fromInt(_IK)];_II=_IL;continue;}}else{var _IO=E(_II);if(!_IO[0]){_IH=_IJ;_II=[1,I_fromInt(_IO[1])];continue;}else{return [1,I_sub(_IJ[1],_IO[1])];}}}},_IP=function(_IQ,_IR,_IS){while(1){if(!E(_IF)){if(!B(_HS(B(_I1(_IR,_IE)),_I0))){if(!B(_HS(_IR,_IB))){var _IT=B(_wt(_IQ,_IQ)),_IU=B(_Im(B(_IG(_IR,_IB)),_IE)),_IV=B(_wt(_IQ,_IS));_IQ=_IT;_IR=_IU;_IS=_IV;continue;}else{return new F(function(){return _wt(_IQ,_IS);});}}else{var _IT=B(_wt(_IQ,_IQ)),_IU=B(_Im(_IR,_IE));_IQ=_IT;_IR=_IU;continue;}}else{return E(_HR);}}},_IW=function(_IX,_IY){while(1){if(!E(_IF)){if(!B(_HS(B(_I1(_IY,_IE)),_I0))){if(!B(_HS(_IY,_IB))){return new F(function(){return _IP(B(_wt(_IX,_IX)),B(_Im(B(_IG(_IY,_IB)),_IE)),_IX);});}else{return E(_IX);}}else{var _IZ=B(_wt(_IX,_IX)),_J0=B(_Im(_IY,_IE));_IX=_IZ;_IY=_J0;continue;}}else{return E(_HR);}}},_J1=function(_J2,_J3){if(!B(_k7(_J3,_I0))){if(!B(_HS(_J3,_I0))){return new F(function(){return _IW(_J2,_J3);});}else{return E(_IB);}}else{return E(_ID);}},_J4=[0,1],_J5=[0,0],_J6=[0,-1],_J7=function(_J8){var _J9=E(_J8);if(!_J9[0]){var _Ja=_J9[1];return (_Ja>=0)?(E(_Ja)==0)?E(_J5):E(_w3):E(_J6);}else{var _Jb=I_compareInt(_J9[1],0);return (_Jb<=0)?(E(_Jb)==0)?E(_J5):E(_J6):E(_w3);}},_Jc=function(_Jd,_Je,_Jf){while(1){var _Jg=E(_Jf);if(!_Jg[0]){if(!B(_k7(_Jd,_wI))){return [0,B(_wt(_Je,B(_J1(_wj,_Jd)))),_IB];}else{var _Jh=B(_J1(_wj,B(_wf(_Jd))));return new F(function(){return _Ix(B(_wt(_Je,B(_J7(_Jh)))),B(_Ih(_Jh)));});}}else{var _Ji=B(_IG(_Jd,_J4)),_Jj=B(_w5(B(_wt(_Je,_wj)),B(_l0(E(_Jg[1])))));_Jf=_Jg[2];_Jd=_Ji;_Je=_Jj;continue;}}},_Jk=function(_Jl,_Jm){var _Jn=E(_Jl);if(!_Jn[0]){var _Jo=_Jn[1],_Jp=E(_Jm);return (_Jp[0]==0)?_Jo>=_Jp[1]:I_compareInt(_Jp[1],_Jo)<=0;}else{var _Jq=_Jn[1],_Jr=E(_Jm);return (_Jr[0]==0)?I_compareInt(_Jq,_Jr[1])>=0:I_compare(_Jq,_Jr[1])>=0;}},_Js=function(_Jt){var _Ju=E(_Jt);if(!_Ju[0]){var _Jv=_Ju[1],_Jw=_Ju[2],_Jx=new T(function(){return B(_wk(_Jw,0));},1),_Jy=new T(function(){return B(_l0(E(_Jv)));});return new F(function(){return _Ix(B(_wt(B(_wJ(_Jy,_Jx,B(_1d(_wp,_Jw)))),_J4)),_J4);});}else{var _Jz=_Ju[1],_JA=_Ju[3],_JB=E(_Ju[2]);if(!_JB[0]){var _JC=E(_JA);if(!_JC[0]){return new F(function(){return _Ix(B(_wt(B(_wZ(_wj,_Jz)),_J4)),_J4);});}else{var _JD=_JC[1];if(!B(_Jk(_JD,_wI))){var _JE=B(_J1(_wj,B(_wf(_JD))));return new F(function(){return _Ix(B(_wt(B(_wZ(_wj,_Jz)),B(_J7(_JE)))),B(_Ih(_JE)));});}else{return new F(function(){return _Ix(B(_wt(B(_wt(B(_wZ(_wj,_Jz)),B(_J1(_wj,_JD)))),_J4)),_J4);});}}}else{var _JF=_JB[1],_JG=E(_JA);if(!_JG[0]){return new F(function(){return _Jc(_wI,B(_wZ(_wj,_Jz)),_JF);});}else{return new F(function(){return _Jc(_JG[1],B(_wZ(_wj,_Jz)),_JF);});}}}},_JH=function(_JI,_JJ){while(1){var _JK=E(_JJ);if(!_JK[0]){return [0];}else{if(!B(A(_JI,[_JK[1]]))){return E(_JK);}else{_JJ=_JK[2];continue;}}}},_JL=function(_JM,_JN){var _JO=E(_JM);if(!_JO[0]){var _JP=_JO[1],_JQ=E(_JN);return (_JQ[0]==0)?_JP>_JQ[1]:I_compareInt(_JQ[1],_JP)<0;}else{var _JR=_JO[1],_JS=E(_JN);return (_JS[0]==0)?I_compareInt(_JR,_JS[1])>0:I_compare(_JR,_JS[1])>0;}},_JT=0,_JU=function(_JV,_JW){return E(_JV)==E(_JW);},_JX=function(_JY){return new F(function(){return _JU(_JT,_JY);});},_JZ=[0,E(_wI),E(_IB)],_K0=[1,_JZ],_K1=[0,-2147483648],_K2=[0,2147483647],_K3=function(_K4,_K5,_K6){var _K7=E(_K6);if(!_K7[0]){return [1,new T(function(){var _K8=B(_Js(_K7));return [0,E(_K8[1]),E(_K8[2])];})];}else{var _K9=E(_K7[3]);if(!_K9[0]){return [1,new T(function(){var _Ka=B(_Js(_K7));return [0,E(_Ka[1]),E(_Ka[2])];})];}else{var _Kb=_K9[1];if(!B(_JL(_Kb,_K2))){if(!B(_k7(_Kb,_K1))){var _Kc=function(_Kd){var _Ke=_Kd+B(_y1(_Kb))|0;if(_Ke<=(E(_K5)+3|0)){if(_Ke>=(E(_K4)-3|0)){return [1,new T(function(){var _Kf=B(_Js(_K7));return [0,E(_Kf[1]),E(_Kf[2])];})];}else{return E(_K0);}}else{return [0];}},_Kg=B(_JH(_JX,_K7[1]));if(!_Kg[0]){var _Kh=E(_K7[2]);if(!_Kh[0]){return E(_K0);}else{var _Ki=B(_qf(_JX,_Kh[1]));if(!E(_Ki[2])[0]){return E(_K0);}else{return new F(function(){return _Kc( -B(_wk(_Ki[1],0)));});}}}else{return new F(function(){return _Kc(B(_wk(_Kg,0)));});}}else{return [0];}}else{return [0];}}}},_Kj=function(_Kk,_Kl){return [2];},_Km=[0,1],_Kn=function(_Ko,_Kp){var _Kq=E(_Ko);if(!_Kq[0]){var _Kr=_Kq[1],_Ks=E(_Kp);if(!_Ks[0]){var _Kt=_Ks[1];return (_Kr!=_Kt)?(_Kr>_Kt)?2:0:1;}else{var _Ku=I_compareInt(_Ks[1],_Kr);return (_Ku<=0)?(_Ku>=0)?1:2:0;}}else{var _Kv=_Kq[1],_Kw=E(_Kp);if(!_Kw[0]){var _Kx=I_compareInt(_Kv,_Kw[1]);return (_Kx>=0)?(_Kx<=0)?1:2:0;}else{var _Ky=I_compare(_Kv,_Kw[1]);return (_Ky>=0)?(_Ky<=0)?1:2:0;}}},_Kz=function(_KA,_KB){var _KC=E(_KA);return (_KC[0]==0)?_KC[1]*Math.pow(2,_KB):I_toNumber(_KC[1])*Math.pow(2,_KB);},_KD=function(_KE,_KF){while(1){var _KG=E(_KE);if(!_KG[0]){var _KH=E(_KG[1]);if(_KH==(-2147483648)){_KE=[1,I_fromInt(-2147483648)];continue;}else{var _KI=E(_KF);if(!_KI[0]){var _KJ=_KI[1];return [0,[0,quot(_KH,_KJ)],[0,_KH%_KJ]];}else{_KE=[1,I_fromInt(_KH)];_KF=_KI;continue;}}}else{var _KK=E(_KF);if(!_KK[0]){_KE=_KG;_KF=[1,I_fromInt(_KK[1])];continue;}else{var _KL=I_quotRem(_KG[1],_KK[1]);return [0,[1,_KL[1]],[1,_KL[2]]];}}}},_KM=[0,0],_KN=function(_KO,_KP,_KQ){if(!B(_HS(_KQ,_KM))){var _KR=B(_KD(_KP,_KQ)),_KS=_KR[1];switch(B(_Kn(B(_li(_KR[2],1)),_KQ))){case 0:return new F(function(){return _Kz(_KS,_KO);});break;case 1:if(!(B(_y1(_KS))&1)){return new F(function(){return _Kz(_KS,_KO);});}else{return new F(function(){return _Kz(B(_w5(_KS,_Km)),_KO);});}break;default:return new F(function(){return _Kz(B(_w5(_KS,_Km)),_KO);});}}else{return E(_HR);}},_KT=function(_KU){var _KV=_w3,_KW=0;while(1){if(!B(_k7(_KV,_KU))){if(!B(_JL(_KV,_KU))){if(!B(_HS(_KV,_KU))){return new F(function(){return _si("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_KW);}}else{return _KW-1|0;}}else{var _KX=B(_li(_KV,1)),_KY=_KW+1|0;_KV=_KX;_KW=_KY;continue;}}},_KZ=function(_L0){var _L1=E(_L0);if(!_L1[0]){var _L2=_L1[1]>>>0;if(!_L2){return -1;}else{var _L3=1,_L4=0;while(1){if(_L3>=_L2){if(_L3<=_L2){if(_L3!=_L2){return new F(function(){return _si("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_L4);}}else{return _L4-1|0;}}else{var _L5=imul(_L3,2)>>>0,_L6=_L4+1|0;_L3=_L5;_L4=_L6;continue;}}}}else{return new F(function(){return _KT(_L1);});}},_L7=function(_L8){var _L9=E(_L8);if(!_L9[0]){var _La=_L9[1]>>>0;if(!_La){return [0,-1,0];}else{var _Lb=function(_Lc,_Ld){while(1){if(_Lc>=_La){if(_Lc<=_La){if(_Lc!=_La){return new F(function(){return _si("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_Ld);}}else{return _Ld-1|0;}}else{var _Le=imul(_Lc,2)>>>0,_Lf=_Ld+1|0;_Lc=_Le;_Ld=_Lf;continue;}}};return [0,B(_Lb(1,0)),(_La&_La-1>>>0)>>>0&4294967295];}}else{var _Lg=B(_KZ(_L9)),_Lh=_Lg>>>0;if(!_Lh){var _Li=E(_Lg);return (_Li==(-2))?[0,-2,0]:[0,_Li,1];}else{var _Lj=function(_Lk,_Ll){while(1){if(_Lk>=_Lh){if(_Lk<=_Lh){if(_Lk!=_Lh){return new F(function(){return _si("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_Ll);}}else{return _Ll-1|0;}}else{var _Lm=imul(_Lk,2)>>>0,_Ln=_Ll+1|0;_Lk=_Lm;_Ll=_Ln;continue;}}},_Lo=B(_Lj(1,0));return ((_Lo+_Lo|0)!=_Lg)?[0,_Lg,1]:[0,_Lg,0];}}},_Lp=function(_Lq,_Lr){while(1){var _Ls=E(_Lq);if(!_Ls[0]){var _Lt=_Ls[1],_Lu=E(_Lr);if(!_Lu[0]){return [0,(_Lt>>>0&_Lu[1]>>>0)>>>0&4294967295];}else{_Lq=[1,I_fromInt(_Lt)];_Lr=_Lu;continue;}}else{var _Lv=E(_Lr);if(!_Lv[0]){_Lq=_Ls;_Lr=[1,I_fromInt(_Lv[1])];continue;}else{return [1,I_and(_Ls[1],_Lv[1])];}}}},_Lw=[0,2],_Lx=function(_Ly,_Lz){var _LA=E(_Ly);if(!_LA[0]){var _LB=(_LA[1]>>>0&(2<<_Lz>>>0)-1>>>0)>>>0,_LC=1<<_Lz>>>0;return (_LC<=_LB)?(_LC>=_LB)?1:2:0;}else{var _LD=B(_Lp(_LA,B(_IG(B(_li(_Lw,_Lz)),_w3)))),_LE=B(_li(_w3,_Lz));return (!B(_JL(_LE,_LD)))?(!B(_k7(_LE,_LD)))?1:2:0;}},_LF=function(_LG,_LH){while(1){var _LI=E(_LG);if(!_LI[0]){_LG=[1,I_fromInt(_LI[1])];continue;}else{return [1,I_shiftRight(_LI[1],_LH)];}}},_LJ=function(_LK,_LL,_LM,_LN){var _LO=B(_L7(_LN)),_LP=_LO[1];if(!E(_LO[2])){var _LQ=B(_KZ(_LM));if(_LQ<((_LP+_LK|0)-1|0)){var _LR=_LP+(_LK-_LL|0)|0;if(_LR>0){if(_LR>_LQ){if(_LR<=(_LQ+1|0)){if(!E(B(_L7(_LM))[2])){return 0;}else{return new F(function(){return _Kz(_Km,_LK-_LL|0);});}}else{return 0;}}else{var _LS=B(_LF(_LM,_LR));switch(B(_Lx(_LM,_LR-1|0))){case 0:return new F(function(){return _Kz(_LS,_LK-_LL|0);});break;case 1:if(!(B(_y1(_LS))&1)){return new F(function(){return _Kz(_LS,_LK-_LL|0);});}else{return new F(function(){return _Kz(B(_w5(_LS,_Km)),_LK-_LL|0);});}break;default:return new F(function(){return _Kz(B(_w5(_LS,_Km)),_LK-_LL|0);});}}}else{return new F(function(){return _Kz(_LM,(_LK-_LL|0)-_LR|0);});}}else{if(_LQ>=_LL){var _LT=B(_LF(_LM,(_LQ+1|0)-_LL|0));switch(B(_Lx(_LM,_LQ-_LL|0))){case 0:return new F(function(){return _Kz(_LT,((_LQ-_LP|0)+1|0)-_LL|0);});break;case 2:return new F(function(){return _Kz(B(_w5(_LT,_Km)),((_LQ-_LP|0)+1|0)-_LL|0);});break;default:if(!(B(_y1(_LT))&1)){return new F(function(){return _Kz(_LT,((_LQ-_LP|0)+1|0)-_LL|0);});}else{return new F(function(){return _Kz(B(_w5(_LT,_Km)),((_LQ-_LP|0)+1|0)-_LL|0);});}}}else{return new F(function(){return _Kz(_LM, -_LP);});}}}else{var _LU=B(_KZ(_LM))-_LP|0,_LV=function(_LW){var _LX=function(_LY,_LZ){if(!B(_y4(B(_li(_LZ,_LL)),_LY))){return new F(function(){return _KN(_LW-_LL|0,_LY,_LZ);});}else{return new F(function(){return _KN((_LW-_LL|0)+1|0,_LY,B(_li(_LZ,1)));});}};if(_LW>=_LL){if(_LW!=_LL){var _M0=new T(function(){return B(_li(_LN,_LW-_LL|0));});return new F(function(){return _LX(_LM,_M0);});}else{return new F(function(){return _LX(_LM,_LN);});}}else{var _M1=new T(function(){return B(_li(_LM,_LL-_LW|0));});return new F(function(){return _LX(_M1,_LN);});}};if(_LK>_LU){return new F(function(){return _LV(_LK);});}else{return new F(function(){return _LV(_LU);});}}},_M2=new T(function(){return 0/0;}),_M3=new T(function(){return -1/0;}),_M4=new T(function(){return 1/0;}),_M5=0,_M6=function(_M7,_M8){if(!B(_HS(_M8,_KM))){if(!B(_HS(_M7,_KM))){if(!B(_k7(_M7,_KM))){return new F(function(){return _LJ(-1021,53,_M7,_M8);});}else{return  -B(_LJ(-1021,53,B(_wf(_M7)),_M8));}}else{return E(_M5);}}else{return (!B(_HS(_M7,_KM)))?(!B(_k7(_M7,_KM)))?E(_M4):E(_M3):E(_M2);}},_M9=function(_Ma){var _Mb=E(_Ma);switch(_Mb[0]){case 3:var _Mc=_Mb[1];return (!B(_1N(_Mc,_Hg)))?(!B(_1N(_Mc,_Hf)))?E(_Kj):E(_Hc):E(_H8);case 5:var _Md=B(_K3(_Hi,_Hh,_Mb[1]));if(!_Md[0]){return E(_H8);}else{var _Me=_Md[1],_Mf=new T(function(){var _Mg=E(_Me);return B(_M6(_Mg[1],_Mg[2]));}),_Mh=function(_Mi,_Mj){return new F(function(){return A(_Mj,[_Mf]);});};return E(_Mh);}break;default:return E(_Kj);}},_Mk=function(_Ml){var _Mm=[3,_Ml,_tS],_Mn=function(_Mo){return E(_Mm);};return [1,function(_Mp){return new F(function(){return A(_E0,[_Mp,_Mn]);});}];},_Mq=new T(function(){return B(A(_GI,[_M9,_G9,_Mk]));}),_Mr=function(_Ms){while(1){var _Mt=(function(_Mu){var _Mv=E(_Mu);if(!_Mv[0]){return [0];}else{var _Mw=_Mv[2],_Mx=E(_Mv[1]);if(!E(_Mx[2])[0]){var _My=new T(function(){return B(_Mr(_Mw));});return [1,_Mx[1],_My];}else{_Ms=_Mw;return null;}}})(_Ms);if(_Mt!=null){return _Mt;}}},_Mz=function(_MA,_MB){var _MC=new T(function(){var _MD=B(_Mr(B(_sm(_Mq,_MA))));if(!_MD[0]){return E(_se);}else{if(!E(_MD[2])[0]){return E(_MD[1])*1.7453292519943295e-2;}else{return E(_sg);}}});return [1,_MC,_MB];},_ME=function(_){return _9;},_MF=new T(function(){return B(unCStr("loadPath"));}),_MG=function(_MH,_){var _MI=function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);},_MJ=_MI,_MK=new T(function(){return E(_MJ);}),_ML=E(_MK)("processDump",toJSStr(_MF));return new F(function(){return _ME(_);});},_MM=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:103:5-17"));}),_MN=[0,_6h,_6i,_2W,_MM,_6h,_6h],_MO=new T(function(){return B(_6f(_MN));}),_MP=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:106:5-19"));}),_MQ=[0,_6h,_6i,_2W,_MP,_6h,_6h],_MR=new T(function(){return B(_6f(_MQ));}),_MS=new T(function(){return B(unCStr("download"));}),_MT=new T(function(){return B(unCStr(".txt"));}),_MU=new T(function(){return B(unCStr(".json"));}),_MV=new T(function(){return B(unCStr("filePath"));}),_MW=new T(function(){return B(unCStr("IndianRoller2.jpg"));}),_MX=15,_MY=[1,_MX,_2W],_MZ=[0,_2t,_2W,_2W,_MY],_N0=function(_N1,_N2){var _N3=E(_N2);if(!_N3[0]){return [0,_2W,_2W];}else{var _N4=_N3[1],_N5=_N3[2];if(!B(A(_N1,[_N4]))){var _N6=new T(function(){var _N7=B(_N0(_N1,_N5));return [0,_N7[1],_N7[2]];}),_N8=new T(function(){return E(E(_N6)[2]);}),_N9=new T(function(){return E(E(_N6)[1]);});return [0,[1,_N4,_N9],_N8];}else{return [0,_2W,_N3];}}},_Na=function(_Nb){var _Nc=_Nb>>>0;if(_Nc>887){var _Nd=u_iswspace(_Nb);return (E(_Nd)==0)?false:true;}else{var _Ne=E(_Nc);return (_Ne==32)?true:(_Ne-9>>>0>4)?(E(_Ne)==160)?true:false:true;}},_Nf=function(_Ng){return new F(function(){return _Na(E(_Ng));});},_Nh=function(_Ni,_Nj,_Nk){var _Nl=function(_Nm){var _Nn=B(_JH(_Nf,_Nm));if(!_Nn[0]){return E(_Nj);}else{var _No=new T(function(){var _Np=B(_N0(_Nf,_Nn));return [0,_Np[1],_Np[2]];}),_Nq=new T(function(){return B(_Nl(E(_No)[2]));}),_Nr=new T(function(){return E(E(_No)[1]);});return new F(function(){return A(_Ni,[_Nr,_Nq]);});}};return new F(function(){return _Nl(_Nk);});},_Ns=function(_){var _Nt=jsFind("filePath");if(!_Nt[0]){return new F(function(){return die(_rR);});}else{var _Nu=jsFind("loadPath");if(!_Nu[0]){return new F(function(){return die(_rU);});}else{var _Nv="runfile",_Nw=jsFind(_Nv);if(!_Nw[0]){return new F(function(){return die(_rX);});}else{var _Nx="rotations",_Ny=jsFind(_Nx);if(!_Ny[0]){return new F(function(){return die(_s0);});}else{var _Nz=nMV(_rO),_NA=_Nz,_NB=nMV(_MZ),_NC=_NB,_ND=B(A(_3,[_6q,_MW,_])),_NE=nMV(_ND),_NF=_NE,_NG=nMV(_MW),_NH=_NG,_NI=B(A(_jc,[_6q,_jj,_])),_NJ=E(_NI);if(!_NJ[0]){return new F(function(){return die(_s3);});}else{var _NK=B(A(_jc,[_6q,_jh,_])),_NL=E(_NK);if(!_NL[0]){return new F(function(){return die(_s6);});}else{var _NM=_NC,_NN=_NF,_NO=function(_){return new F(function(){return _mV(_NM,_NA,_NN,_);});},_NP=B(_oD(_NA,_NJ[1],_NO,_)),_NQ=B(_ra(_NM,_NL[1],_NO,_)),_NR=function(_NS,_){var _NT=String(E(_NS)),_NU=jsParseJSON(_NT);if(!_NU[0]){return _8V;}else{var _NV=B(_3M(_NU[1]));if(!_NV[0]){return _8V;}else{var _NW=_NV[1],_NX=new T(function(){return E(E(_NW)[1]);}),_=wMV(_NA,_NX),_NY=new T(function(){return E(E(_NW)[2]);}),_=wMV(_NC,_NY);return _8V;}}},_NZ=__createJSFunc(2,E(_NR)),_O0=(function(s,f){Haste[s] = f;}),_O1=_O0,_O2=new T(function(){return E(_O1);}),_O3=E(_O2)("processDump",_NZ),_O4=function(_O5,_){var _O6=E(_O5),_O7=toJSStr(_MV),_O8=E(_rE)(_O7),_O9=_O8,_Oa=new T(function(){var _Ob=String(_O9);return fromJSStr(_Ob);}),_Oc=B(A(_3,[_6q,_Oa,_])),_=wMV(_NF,_Oc),_Od=E(_rF)(_O7),_Oe=_Od,_Of=new T(function(){var _Og=String(_Oe);return fromJSStr(_Og);}),_=wMV(_NH,_Of),_Oh=jsFind(toJSStr(E(_iW)));if(!_Oh[0]){return new F(function(){return die(_MO);});}else{var _Oi=new T(function(){return B(_G(_Of,_MU));}),_Oj=B(A(_fk,[_s,_6q,_Oh[1],_MS,_Oi,_])),_Ok=jsFind(toJSStr(E(_iX)));if(!_Ok[0]){return new F(function(){return die(_MR);});}else{var _Ol=new T(function(){return B(_G(_Of,_MT));}),_Om=B(A(_fk,[_s,_6q,_Ok[1],_MS,_Ol,_]));return new F(function(){return _mV(_NM,_NA,_NN,_);});}}},_On=B(A(_bS,[_6r,_s,_n,_Nt[1],_be,_O4,_])),_Oo=B(A(_bS,[_6r,_s,_n,_Nu[1],_be,_MG,_])),_Op=function(_){var _Oq=jsFind(_Nv);if(!_Oq[0]){return new F(function(){return die(_s9);});}else{var _Or=jsFind(_Nx);if(!_Or[0]){return new F(function(){return die(_sc);});}else{var _Os=B(A(_mh,[_s,_6q,_Oq[1],_j5,_])),_Ot=rMV(_NC),_Ou=E(_Ot),_=wMV(_NC,[0,_Ou[1],_Ou[2],_Os,_Ou[4]]),_Ov=B(A(_mh,[_s,_6q,_Or[1],_j5,_])),_Ow=_Ov,_Ox=rMV(_NC),_Oy=E(_Ox),_Oz=new T(function(){return B(_Nh(_Mz,_2W,_Ow));}),_=wMV(_NC,[0,_Oy[1],_Oy[2],_Oy[3],_Oz]);return new F(function(){return _mV(_NM,_NA,_NN,_);});}}},_OA=function(_OB,_){return new F(function(){return _Op(_);});},_OC=B(A(_bS,[_6r,_s,_n,_Nw[1],_be,_OA,_])),_OD=function(_OE,_){return new F(function(){return _Op(_);});},_OF=B(A(_bS,[_6r,_s,_n,_Ny[1],_be,_OD,_]));return new F(function(){return _mV(_NM,_NA,_NN,_);});}}}}}}},_OG=function(_){return new F(function(){return _Ns(_);});};
var hasteMain = function() {B(A(_OG, [0]));};window.onload = hasteMain;