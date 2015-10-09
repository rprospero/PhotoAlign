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

var _0="src",_1=function(_2){return E(E(_2)[2]);},_3=function(_4,_5){var _6=function(_){var _7=jsCreateElem("img"),_8=jsSet(_7,E(_0),toJSStr(E(_5)));return _7;};return new F(function(){return A(_1,[_4,_6]);});},_9=0,_a=function(_){return _9;},_b=function(_c,_d,_){return new F(function(){return _a(_);});},_e="scroll",_f="submit",_g="blur",_h="focus",_i="change",_j="unload",_k="load",_l=function(_m){switch(E(_m)){case 0:return E(_k);case 1:return E(_j);case 2:return E(_i);case 3:return E(_h);case 4:return E(_g);case 5:return E(_f);default:return E(_e);}},_n=[0,_l,_b],_o="metaKey",_p="shiftKey",_q="altKey",_r="ctrlKey",_s="keyCode",_t=function(_u,_){var _v=_u[E(_s)],_w=_v,_x=_u[E(_r)],_y=_x,_z=_u[E(_q)],_A=_z,_B=_u[E(_p)],_C=_B,_D=_u[E(_o)],_E=_D;return new T(function(){var _F=Number(_w),_G=jsTrunc(_F);return [0,_G,E(_y),E(_A),E(_C),E(_E)];});},_H=function(_I,_J,_){return new F(function(){return _t(E(_J),_);});},_K="keydown",_L="keyup",_M="keypress",_N=function(_O){switch(E(_O)){case 0:return E(_M);case 1:return E(_L);default:return E(_K);}},_P=[0,_N,_H],_Q=function(_R,_){return [1,_R];},_S=function(_T){return E(_T);},_U=[0,_S,_Q],_V=function(_W){return E(E(_W)[1]);},_X=function(_Y,_Z){return (!B(A(_V,[_10,_Y,_Z])))?true:false;},_11=function(_12,_13){var _14=strEq(E(_12),E(_13));return (E(_14)==0)?false:true;},_15=function(_16,_17){return new F(function(){return _11(_16,_17);});},_10=new T(function(){return [0,_15,_X];}),_18=function(_19,_1a){var _1b=E(_19);if(!_1b[0]){return E(_1a);}else{var _1c=_1b[2],_1d=new T(function(){return B(_18(_1c,_1a));});return [1,_1b[1],_1d];}},_1e=new T(function(){return B(unCStr("!!: negative index"));}),_1f=new T(function(){return B(unCStr("Prelude."));}),_1g=new T(function(){return B(_18(_1f,_1e));}),_1h=new T(function(){return B(err(_1g));}),_1i=new T(function(){return B(unCStr("!!: index too large"));}),_1j=new T(function(){return B(_18(_1f,_1i));}),_1k=new T(function(){return B(err(_1j));}),_1l=function(_1m,_1n){while(1){var _1o=E(_1m);if(!_1o[0]){return E(_1k);}else{var _1p=E(_1n);if(!_1p){return E(_1o[1]);}else{_1m=_1o[2];_1n=_1p-1|0;continue;}}}},_1q=function(_1r,_1s){if(_1s>=0){return new F(function(){return _1l(_1r,_1s);});}else{return E(_1h);}},_1t=new T(function(){return B(unCStr(": empty list"));}),_1u=function(_1v){var _1w=new T(function(){return B(_18(_1v,_1t));},1);return new F(function(){return err(B(_18(_1f,_1w)));});},_1x=new T(function(){return B(unCStr("head"));}),_1y=new T(function(){return B(_1u(_1x));}),_1z=function(_1A){var _1B=E(_1A);if(_1B[0]==3){var _1C=E(_1B[1]);if(!_1C[0]){return E(_1y);}else{var _1D=E(_1C[1]);if(!_1D[0]){var _1E=B(_1q(_1C,1));return (_1E[0]==0)?[1,[0,_1D[1],_1E[1]]]:[0];}else{return [0];}}}else{return [0];}},_1F=function(_1G,_1H){var _1I=E(_1H);if(!_1I[0]){return [0];}else{var _1J=_1I[1],_1K=_1I[2],_1L=new T(function(){return B(_1F(_1G,_1K));}),_1M=new T(function(){return B(A(_1G,[_1J]));});return [1,_1M,_1L];}},_1N=function(_1O){var _1P=E(_1O);if(_1P[0]==3){var _1Q=B(_1F(_1z,_1P[1]));if(!_1Q[0]){return E(_1y);}else{var _1R=E(_1Q[1]);if(!_1R[0]){return [0];}else{var _1S=B(_1q(_1Q,1));if(!_1S[0]){return [0];}else{var _1T=B(_1q(_1Q,2));if(!_1T[0]){return [0];}else{var _1U=B(_1q(_1Q,3));return (_1U[0]==0)?[0]:[1,[0,_1R[1],_1S[1],_1T[1],_1U[1]]];}}}}}else{return [0];}},_1V="box",_1W="mouse",_1X="corner",_1Y="Dragging",_1Z=[0],_20=[1,_1Z],_21="Free",_22="state",_23=1,_24=[1,_23],_25=0,_26=[1,_25],_27=3,_28=[1,_27],_29=2,_2a=[1,_29],_2b=new T(function(){return B(unCStr("SW"));}),_2c=new T(function(){return B(unCStr("SE"));}),_2d=new T(function(){return B(unCStr("NW"));}),_2e=new T(function(){return B(unCStr("NE"));}),_2f=function(_2g,_2h){while(1){var _2i=E(_2g);if(!_2i[0]){return (E(_2h)[0]==0)?true:false;}else{var _2j=E(_2h);if(!_2j[0]){return false;}else{if(E(_2i[1])!=E(_2j[1])){return false;}else{_2g=_2i[2];_2h=_2j[2];continue;}}}}},_2k=function(_2l){var _2m=E(_2l);if(_2m[0]==1){var _2n=fromJSStr(_2m[1]);return (!B(_2f(_2n,_2e)))?(!B(_2f(_2n,_2d)))?(!B(_2f(_2n,_2c)))?(!B(_2f(_2n,_2b)))?[0]:E(_2a):E(_28):E(_26):E(_24);}else{return [0];}},_2o=function(_2p,_2q,_2r){while(1){var _2s=E(_2r);if(!_2s[0]){return [0];}else{var _2t=E(_2s[1]);if(!B(A(_V,[_2p,_2q,_2t[1]]))){_2r=_2s[2];continue;}else{return [1,_2t[2]];}}}},_2u=function(_2v){var _2w=E(_2v);if(_2w[0]==4){var _2x=_2w[1],_2y=B(_2o(_10,_22,_2x));if(!_2y[0]){return [0];}else{var _2z=E(_2y[1]);if(_2z[0]==1){var _2A=_2z[1],_2B=strEq(_2A,E(_21));if(!E(_2B)){var _2C=strEq(_2A,E(_1Y));if(!E(_2C)){return [0];}else{var _2D=B(_2o(_10,_1X,_2x));if(!_2D[0]){return [0];}else{var _2E=B(_2k(_2D[1]));return (_2E[0]==0)?[0]:[1,[1,_2E[1]]];}}}else{return E(_20);}}else{return [0];}}}else{return [0];}},_2F=function(_2G){var _2H=E(_2G);if(_2H[0]==4){var _2I=_2H[1],_2J=B(_2o(_10,_1W,_2I));if(!_2J[0]){return [0];}else{var _2K=B(_2u(_2J[1]));if(!_2K[0]){return [0];}else{var _2L=B(_2o(_10,_1V,_2I));if(!_2L[0]){return [0];}else{var _2M=B(_1N(_2L[1]));return (_2M[0]==0)?[0]:[1,[0,_2K[1],_2M[1]]];}}}}else{return [0];}},_2N=function(_2O){return [0,E(_2O)];},_2P=function(_2Q){var _2R=E(_2Q);return (_2R[0]==0)?[1,_2R[1]]:[0];},_2S=[0,_2N,_2P],_2T=1,_2U=[1,_2T],_2V=0,_2W=[1,_2V],_2X=new T(function(){return B(unCStr("Top"));}),_2Y=new T(function(){return B(unCStr("Bottom"));}),_2Z=function(_30){var _31=E(_30);if(_31[0]==1){var _32=fromJSStr(_31[1]);return (!B(_2f(_32,_2Y)))?(!B(_2f(_32,_2X)))?[0]:E(_2W):E(_2U);}else{return [0];}},_33=1,_34=[1,_33],_35=0,_36=[1,_35],_37=new T(function(){return B(unCStr("Free"));}),_38=new T(function(){return B(unCStr("Dragging"));}),_39=function(_3a){var _3b=E(_3a);if(_3b[0]==1){var _3c=fromJSStr(_3b[1]);return (!B(_2f(_3c,_38)))?(!B(_2f(_3c,_37)))?[0]:E(_36):E(_34);}else{return [0];}},_3d="title",_3e="points",_3f=function(_3g){var _3h=E(_3g);if(_3h[0]==4){var _3i=_3h[1],_3j=B(_2o(_10,_3e,_3i));if(!_3j[0]){return [0];}else{var _3k=E(_3j[1]);if(_3k[0]==3){var _3l=E(_3k[1]);if(!_3l[0]){return E(_1y);}else{var _3m=E(_3l[1]);if(_3m[0]==3){var _3n=E(_3m[1]);if(!_3n[0]){return E(_1y);}else{var _3o=E(_3n[1]);if(!_3o[0]){var _3p=B(_1q(_3n,1));if(!_3p[0]){var _3q=B(_1q(_3l,1));if(_3q[0]==3){var _3r=E(_3q[1]);if(!_3r[0]){return E(_1y);}else{var _3s=E(_3r[1]);if(!_3s[0]){var _3t=B(_1q(_3r,1));if(!_3t[0]){var _3u=B(_2o(_10,_3d,_3i));if(!_3u[0]){return [0];}else{var _3v=E(_3u[1]);if(_3v[0]==1){var _3w=_3v[1],_3x=new T(function(){return fromJSStr(_3w);});return [1,[0,[0,_3o[1],_3p[1]],[0,_3s[1],_3t[1]],_3x]];}else{return [0];}}}else{return [0];}}else{return [0];}}}else{return [0];}}else{return [0];}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}},_3y=[0],_3z=function(_3A){var _3B=new T(function(){var _3C=E(E(_3A)[2]),_3D=_3C[1],_3E=_3C[2],_3F=new T(function(){return B(_2N(_3E));}),_3G=new T(function(){return B(_2N(_3D));});return [3,[1,_3G,[1,_3F,_3y]]];}),_3H=new T(function(){var _3I=E(E(_3A)[1]),_3J=_3I[1],_3K=_3I[2],_3L=new T(function(){return B(_2N(_3K));}),_3M=new T(function(){return B(_2N(_3J));});return [3,[1,_3M,[1,_3L,_3y]]];}),_3N=new T(function(){return [1,toJSStr(E(E(_3A)[3]))];});return [1,[0,_3d,_3N],[1,[0,_3e,[3,[1,_3H,[1,_3B,_3y]]]],_3y]];},_3O=function(_3P){return [4,E(B(_3z(_3P)))];},_3Q=[0,_3O,_3f],_3R="rotations",_3S="choice",_3T="offset",_3U="bottom",_3V="top",_3W="fileName",_3X="scans",_3Y="mouse",_3Z=[1,_3y],_40=function(_41){return E(E(_41)[2]);},_42=function(_43,_44){var _45=E(_44);if(_45[0]==3){var _46=new T(function(){return B(_40(_43));}),_47=function(_48){var _49=E(_48);if(!_49[0]){return E(_3Z);}else{var _4a=B(A(_46,[_49[1]]));if(!_4a[0]){return [0];}else{var _4b=B(_47(_49[2]));return (_4b[0]==0)?[0]:[1,[1,_4a[1],_4b[1]]];}}};return new F(function(){return _47(_45[1]);});}else{return [0];}},_4c=function(_4d){var _4e=E(_4d);if(_4e[0]==4){var _4f=_4e[1],_4g=B(_2o(_10,_3Y,_4f));if(!_4g[0]){return [0];}else{var _4h=B(_39(_4g[1]));if(!_4h[0]){return [0];}else{var _4i=B(_2o(_10,_3X,_4f));if(!_4i[0]){return [0];}else{var _4j=B(_42(_3Q,_4i[1]));if(!_4j[0]){return [0];}else{var _4k=B(_2o(_10,_3W,_4f));if(!_4k[0]){return [0];}else{var _4l=E(_4k[1]);if(_4l[0]==1){var _4m=_4l[1],_4n=B(_2o(_10,_3V,_4f));if(!_4n[0]){return [0];}else{var _4o=E(_4n[1]);if(!_4o[0]){var _4p=B(_2o(_10,_3U,_4f));if(!_4p[0]){return [0];}else{var _4q=E(_4p[1]);if(!_4q[0]){var _4r=B(_2o(_10,_3T,_4f));if(!_4r[0]){return [0];}else{var _4s=E(_4r[1]);if(!_4s[0]){var _4t=B(_2o(_10,_3S,_4f));if(!_4t[0]){return [0];}else{var _4u=B(_2Z(_4t[1]));if(!_4u[0]){return [0];}else{var _4v=B(_2o(_10,_3R,_4f));if(!_4v[0]){return [0];}else{var _4w=B(_42(_2S,_4v[1]));if(!_4w[0]){return [0];}else{var _4x=new T(function(){return fromJSStr(_4m);});return [1,[0,_4h[1],_4j[1],_4x,_4o[1],_4q[1],_4s[1],_4u[1],_4w[1]]];}}}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}}}}}else{return [0];}},_4y="scans",_4z="calib",_4A=function(_4B){var _4C=E(_4B);if(_4C[0]==4){var _4D=_4C[1],_4E=B(_2o(_10,_4z,_4D));if(!_4E[0]){return [0];}else{var _4F=B(_2F(_4E[1]));if(!_4F[0]){return [0];}else{var _4G=B(_2o(_10,_4y,_4D));if(!_4G[0]){return [0];}else{var _4H=B(_4c(_4G[1]));return (_4H[0]==0)?[0]:[1,[0,_4F[1],_4H[1]]];}}}}else{return [0];}},_4I=function(_4J,_4K,_){var _4L=B(A(_4J,[_])),_4M=B(A(_4K,[_]));return _4L;},_4N=function(_4O,_4P,_){var _4Q=B(A(_4O,[_])),_4R=_4Q,_4S=B(A(_4P,[_])),_4T=_4S;return new T(function(){return B(A(_4R,[_4T]));});},_4U=function(_4V,_4W,_){var _4X=B(A(_4W,[_]));return _4V;},_4Y=function(_4Z,_50,_){var _51=B(A(_50,[_])),_52=_51;return new T(function(){return B(A(_4Z,[_52]));});},_53=[0,_4Y,_4U],_54=function(_55,_){return _55;},_56=function(_57,_58,_){var _59=B(A(_57,[_]));return new F(function(){return A(_58,[_]);});},_5a=[0,_53,_54,_4N,_56,_4I],_5b=function(_5c,_5d,_){var _5e=B(A(_5c,[_]));return new F(function(){return A(_5d,[_5e,_]);});},_5f=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_5g=new T(function(){return B(unCStr("base"));}),_5h=new T(function(){return B(unCStr("IOException"));}),_5i=new T(function(){var _5j=hs_wordToWord64(4053623282),_5k=hs_wordToWord64(3693590983);return [0,_5j,_5k,[0,_5j,_5k,_5g,_5f,_5h],_3y,_3y];}),_5l=function(_5m){return E(_5i);},_5n=function(_5o){return E(E(_5o)[1]);},_5p=function(_5q,_5r,_5s){var _5t=B(A(_5q,[_])),_5u=B(A(_5r,[_])),_5v=hs_eqWord64(_5t[1],_5u[1]);if(!_5v){return [0];}else{var _5w=hs_eqWord64(_5t[2],_5u[2]);return (!_5w)?[0]:[1,_5s];}},_5x=function(_5y){var _5z=E(_5y);return new F(function(){return _5p(B(_5n(_5z[1])),_5l,_5z[2]);});},_5A=new T(function(){return B(unCStr(": "));}),_5B=new T(function(){return B(unCStr(")"));}),_5C=new T(function(){return B(unCStr(" ("));}),_5D=new T(function(){return B(unCStr("interrupted"));}),_5E=new T(function(){return B(unCStr("system error"));}),_5F=new T(function(){return B(unCStr("unsatisified constraints"));}),_5G=new T(function(){return B(unCStr("user error"));}),_5H=new T(function(){return B(unCStr("permission denied"));}),_5I=new T(function(){return B(unCStr("illegal operation"));}),_5J=new T(function(){return B(unCStr("end of file"));}),_5K=new T(function(){return B(unCStr("resource exhausted"));}),_5L=new T(function(){return B(unCStr("resource busy"));}),_5M=new T(function(){return B(unCStr("does not exist"));}),_5N=new T(function(){return B(unCStr("already exists"));}),_5O=new T(function(){return B(unCStr("resource vanished"));}),_5P=new T(function(){return B(unCStr("timeout"));}),_5Q=new T(function(){return B(unCStr("unsupported operation"));}),_5R=new T(function(){return B(unCStr("hardware fault"));}),_5S=new T(function(){return B(unCStr("inappropriate type"));}),_5T=new T(function(){return B(unCStr("invalid argument"));}),_5U=new T(function(){return B(unCStr("failed"));}),_5V=new T(function(){return B(unCStr("protocol error"));}),_5W=function(_5X,_5Y){switch(E(_5X)){case 0:return new F(function(){return _18(_5N,_5Y);});break;case 1:return new F(function(){return _18(_5M,_5Y);});break;case 2:return new F(function(){return _18(_5L,_5Y);});break;case 3:return new F(function(){return _18(_5K,_5Y);});break;case 4:return new F(function(){return _18(_5J,_5Y);});break;case 5:return new F(function(){return _18(_5I,_5Y);});break;case 6:return new F(function(){return _18(_5H,_5Y);});break;case 7:return new F(function(){return _18(_5G,_5Y);});break;case 8:return new F(function(){return _18(_5F,_5Y);});break;case 9:return new F(function(){return _18(_5E,_5Y);});break;case 10:return new F(function(){return _18(_5V,_5Y);});break;case 11:return new F(function(){return _18(_5U,_5Y);});break;case 12:return new F(function(){return _18(_5T,_5Y);});break;case 13:return new F(function(){return _18(_5S,_5Y);});break;case 14:return new F(function(){return _18(_5R,_5Y);});break;case 15:return new F(function(){return _18(_5Q,_5Y);});break;case 16:return new F(function(){return _18(_5P,_5Y);});break;case 17:return new F(function(){return _18(_5O,_5Y);});break;default:return new F(function(){return _18(_5D,_5Y);});}},_5Z=new T(function(){return B(unCStr("}"));}),_60=new T(function(){return B(unCStr("{handle: "));}),_61=function(_62,_63,_64,_65,_66,_67){var _68=new T(function(){var _69=new T(function(){var _6a=new T(function(){var _6b=E(_65);if(!_6b[0]){return E(_67);}else{var _6c=new T(function(){var _6d=new T(function(){return B(_18(_5B,_67));},1);return B(_18(_6b,_6d));},1);return B(_18(_5C,_6c));}},1);return B(_5W(_63,_6a));}),_6e=E(_64);if(!_6e[0]){return E(_69);}else{var _6f=new T(function(){return B(_18(_5A,_69));},1);return B(_18(_6e,_6f));}}),_6g=E(_66);if(!_6g[0]){var _6h=E(_62);if(!_6h[0]){return E(_68);}else{var _6i=E(_6h[1]);if(!_6i[0]){var _6j=_6i[1],_6k=new T(function(){var _6l=new T(function(){var _6m=new T(function(){return B(_18(_5A,_68));},1);return B(_18(_5Z,_6m));},1);return B(_18(_6j,_6l));},1);return new F(function(){return _18(_60,_6k);});}else{var _6n=_6i[1],_6o=new T(function(){var _6p=new T(function(){var _6q=new T(function(){return B(_18(_5A,_68));},1);return B(_18(_5Z,_6q));},1);return B(_18(_6n,_6p));},1);return new F(function(){return _18(_60,_6o);});}}}else{var _6r=new T(function(){return B(_18(_5A,_68));},1);return new F(function(){return _18(_6g[1],_6r);});}},_6s=function(_6t){var _6u=E(_6t);return new F(function(){return _61(_6u[1],_6u[2],_6u[3],_6u[4],_6u[6],_3y);});},_6v=function(_6w,_6x,_6y){var _6z=E(_6x);return new F(function(){return _61(_6z[1],_6z[2],_6z[3],_6z[4],_6z[6],_6y);});},_6A=function(_6B,_6C){var _6D=E(_6B);return new F(function(){return _61(_6D[1],_6D[2],_6D[3],_6D[4],_6D[6],_6C);});},_6E=44,_6F=93,_6G=91,_6H=function(_6I,_6J,_6K){var _6L=E(_6J);if(!_6L[0]){return new F(function(){return unAppCStr("[]",_6K);});}else{var _6M=_6L[1],_6N=_6L[2],_6O=new T(function(){var _6P=new T(function(){var _6Q=[1,_6F,_6K],_6R=function(_6S){var _6T=E(_6S);if(!_6T[0]){return E(_6Q);}else{var _6U=_6T[1],_6V=_6T[2],_6W=new T(function(){var _6X=new T(function(){return B(_6R(_6V));});return B(A(_6I,[_6U,_6X]));});return [1,_6E,_6W];}};return B(_6R(_6N));});return B(A(_6I,[_6M,_6P]));});return [1,_6G,_6O];}},_6Y=function(_6Z,_70){return new F(function(){return _6H(_6A,_6Z,_70);});},_71=[0,_6v,_6s,_6Y],_72=new T(function(){return [0,_5l,_71,_73,_5x,_6s];}),_73=function(_74){return [0,_72,_74];},_75=[0],_76=7,_77=function(_78){return [0,_75,_76,_3y,_78,_75,_75];},_79=function(_7a,_){var _7b=new T(function(){var _7c=new T(function(){return B(_77(_7a));});return B(_73(_7c));});return new F(function(){return die(_7b);});},_7d=[0,_5a,_5b,_56,_54,_79],_7e=[0,_7d,_S],_7f=[0,_7e,_54],_7g=function(_7h,_7i,_7j,_7k,_7l,_7m,_7n,_7o){if(_7h!=_7l){return false;}else{if(E(_7i)!=E(_7m)){return false;}else{var _7p=E(_7j),_7q=E(_7n);if(E(_7p[1])!=E(_7q[1])){return false;}else{if(E(_7p[2])!=E(_7q[2])){return false;}else{return new F(function(){return _2f(_7k,_7o);});}}}}},_7r=function(_7s,_7t){var _7u=E(_7s),_7v=E(_7u[1]),_7w=E(_7t),_7x=E(_7w[1]);return new F(function(){return _7g(E(_7v[1]),_7v[2],_7u[2],_7u[3],E(_7x[1]),_7x[2],_7w[2],_7w[3]);});},_7y="scans",_7z=[1,_7y,_3y],_7A="calib",_7B=[1,_7A,_7z],_7C=function(_7D){var _7E=E(_7D),_7F=_7E[1],_7G=_7E[2],_7H=new T(function(){return B(_2N(_7G));}),_7I=new T(function(){return B(_2N(_7F));});return [3,[1,_7I,[1,_7H,_3y]]];},_7J=new T(function(){return [1,"Dragging"];}),_7K=[0,_22,_7J],_7L=new T(function(){return [1,"Free"];}),_7M="state",_7N=[0,_7M,_7L],_7O=[1,_7N,_3y],_7P=[4,E(_7O)],_7Q=function(_7R,_7S){switch(E(_7R)){case 0:return new F(function(){return _18(_2d,_7S);});break;case 1:return new F(function(){return _18(_2e,_7S);});break;case 2:return new F(function(){return _18(_2b,_7S);});break;default:return new F(function(){return _18(_2c,_7S);});}},_7T=function(_7U){return E(toJSStr(B(_7Q(_7U,_3y))));},_7V=function(_7W){return [1,B(_7T(_7W))];},_7X=function(_7Y){var _7Z=new T(function(){var _80=E(E(_7Y)[2]),_81=_80[1],_82=_80[2],_83=_80[3],_84=_80[4],_85=new T(function(){return B(_7C(_84));}),_86=new T(function(){return B(_7C(_83));}),_87=new T(function(){return B(_7C(_82));}),_88=new T(function(){return B(_7C(_81));});return [3,[1,_88,[1,_87,[1,_86,[1,_85,_3y]]]]];}),_89=new T(function(){var _8a=E(E(_7Y)[1]);if(!_8a[0]){return E(_7P);}else{var _8b=_8a[1],_8c=new T(function(){return B(_7V(_8b));});return [4,[1,_7K,[1,[0,_1X,_8c],_3y]]];}});return [1,[0,_1W,_89],[1,[0,_1V,_7Z],_3y]];},_8d="rotations",_8e=[1,_8d,_3y],_8f="choice",_8g=[1,_8f,_8e],_8h="offset",_8i=[1,_8h,_8g],_8j="bottom",_8k=[1,_8j,_8i],_8l="top",_8m=[1,_8l,_8k],_8n="fileName",_8o=[1,_8n,_8m],_8p="scans",_8q=[1,_8p,_8o],_8r="mouse",_8s=[1,_8r,_8q],_8t=function(_8u,_8v){var _8w=E(_8u);if(!_8w[0]){return [0];}else{var _8x=_8w[2],_8y=E(_8v);if(!_8y[0]){return [0];}else{var _8z=_8y[2],_8A=new T(function(){return B(_8t(_8x,_8z));});return [1,[0,_8w[1],_8y[1]],_8A];}}},_8B=function(_8C){var _8D=new T(function(){return [3,E(B(_1F(_2N,E(_8C)[8])))];}),_8E=new T(function(){if(!E(E(_8C)[7])){return [1,toJSStr(E(_2X))];}else{return [1,toJSStr(E(_2Y))];}}),_8F=new T(function(){return [0,E(E(_8C)[6])];}),_8G=new T(function(){return [0,E(E(_8C)[5])];}),_8H=new T(function(){return [0,E(E(_8C)[4])];}),_8I=new T(function(){return [1,toJSStr(E(E(_8C)[3]))];}),_8J=new T(function(){return [3,E(B(_1F(_3O,E(_8C)[2])))];}),_8K=new T(function(){if(!E(E(_8C)[1])){return [1,toJSStr(E(_37))];}else{return [1,toJSStr(E(_38))];}});return new F(function(){return _8t(_8s,[1,_8K,[1,_8J,[1,_8I,[1,_8H,[1,_8G,[1,_8F,[1,_8E,[1,_8D,_3y]]]]]]]]);});},_8L=function(_8M){return [1,E(_8M)];},_8N="deltaZ",_8O="deltaY",_8P="deltaX",_8Q=function(_8R,_8S){var _8T=jsShowI(_8R);return new F(function(){return _18(fromJSStr(_8T),_8S);});},_8U=41,_8V=40,_8W=function(_8X,_8Y,_8Z){if(_8Y>=0){return new F(function(){return _8Q(_8Y,_8Z);});}else{if(_8X<=6){return new F(function(){return _8Q(_8Y,_8Z);});}else{var _90=new T(function(){var _91=jsShowI(_8Y);return B(_18(fromJSStr(_91),[1,_8U,_8Z]));});return [1,_8V,_90];}}},_92=new T(function(){return B(unCStr(")"));}),_93=new T(function(){return B(_8W(0,2,_92));}),_94=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_93));}),_95=function(_96){var _97=new T(function(){return B(_8W(0,_96,_94));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_97)));});},_98=function(_99,_){return new T(function(){var _9a=Number(E(_99)),_9b=jsTrunc(_9a);if(_9b<0){return B(_95(_9b));}else{if(_9b>2){return B(_95(_9b));}else{return _9b;}}});},_9c=0,_9d=[0,_9c,_9c,_9c],_9e="button",_9f=new T(function(){return jsGetMouseCoords;}),_9g=function(_9h,_){var _9i=E(_9h);if(!_9i[0]){return _3y;}else{var _9j=_9i[1],_9k=B(_9g(_9i[2],_)),_9l=new T(function(){var _9m=Number(E(_9j));return jsTrunc(_9m);});return [1,_9l,_9k];}},_9n=function(_9o,_){var _9p=__arr2lst(0,_9o);return new F(function(){return _9g(_9p,_);});},_9q=function(_9r,_){return new F(function(){return _9n(E(_9r),_);});},_9s=function(_9t,_){return new T(function(){var _9u=Number(E(_9t));return jsTrunc(_9u);});},_9v=[0,_9s,_9q],_9w=function(_9x,_){var _9y=E(_9x);if(!_9y[0]){return _3y;}else{var _9z=B(_9w(_9y[2],_));return [1,_9y[1],_9z];}},_9A=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_9B=[0,_75,_76,_3y,_9A,_75,_75],_9C=new T(function(){return B(_73(_9B));}),_9D=function(_){return new F(function(){return die(_9C);});},_9E=function(_9F){return E(E(_9F)[1]);},_9G=function(_9H,_9I,_9J,_){var _9K=__arr2lst(0,_9J),_9L=B(_9w(_9K,_)),_9M=E(_9L);if(!_9M[0]){return new F(function(){return _9D(_);});}else{var _9N=E(_9M[2]);if(!_9N[0]){return new F(function(){return _9D(_);});}else{if(!E(_9N[2])[0]){var _9O=B(A(_9E,[_9H,_9M[1],_])),_9P=B(A(_9E,[_9I,_9N[1],_]));return [0,_9O,_9P];}else{return new F(function(){return _9D(_);});}}}},_9Q=function(_){return new F(function(){return __jsNull();});},_9R=function(_9S){var _9T=B(A(_9S,[_]));return E(_9T);},_9U=new T(function(){return B(_9R(_9Q));}),_9V=new T(function(){return E(_9U);}),_9W=function(_9X,_9Y,_){if(E(_9X)==7){var _9Z=E(_9f)(_9Y),_a0=B(_9G(_9v,_9v,_9Z,_)),_a1=_a0,_a2=_9Y[E(_8P)],_a3=_a2,_a4=_9Y[E(_8O)],_a5=_a4,_a6=_9Y[E(_8N)],_a7=_a6;return new T(function(){return [0,E(_a1),E(_75),[0,_a3,_a5,_a7]];});}else{var _a8=E(_9f)(_9Y),_a9=B(_9G(_9v,_9v,_a8,_)),_aa=_a9,_ab=_9Y[E(_9e)],_ac=__eq(_ab,E(_9V));if(!E(_ac)){var _ad=B(_98(_ab,_)),_ae=_ad;return new T(function(){return [0,E(_aa),[1,_ae],E(_9d)];});}else{return new T(function(){return [0,E(_aa),E(_75),E(_9d)];});}}},_af=function(_ag,_ah,_){return new F(function(){return _9W(_ag,E(_ah),_);});},_ai="mouseout",_aj="mouseover",_ak="mousemove",_al="mouseup",_am="mousedown",_an="dblclick",_ao="click",_ap="wheel",_aq=function(_ar){switch(E(_ar)){case 0:return E(_ao);case 1:return E(_an);case 2:return E(_am);case 3:return E(_al);case 4:return E(_ak);case 5:return E(_aj);case 6:return E(_ai);default:return E(_ap);}},_as=[0,_aq,_af],_at=function(_){return new F(function(){return jsCreateElem("th");});},_au=function(_av,_aw){var _ax=function(_){return new F(function(){return jsCreateTextNode(toJSStr(E(_aw)));});};return new F(function(){return A(_1,[_av,_ax]);});},_ay=function(_az){return E(E(_az)[1]);},_aA=function(_aB){return E(E(_aB)[3]);},_aC=function(_aD){return E(E(_aD)[2]);},_aE=function(_aF){return E(E(_aF)[4]);},_aG=function(_aH){return E(E(_aH)[1]);},_aI=function(_aJ,_aK,_aL,_aM){var _aN=new T(function(){return B(A(_aG,[_aJ,_aL]));}),_aO=function(_aP,_){var _aQ=E(_aP);if(!_aQ[0]){return _9;}else{var _aR=E(_aN),_aS=jsAppendChild(E(_aQ[1]),_aR),_aT=_aQ[2],_=_;while(1){var _aU=E(_aT);if(!_aU[0]){return _9;}else{var _aV=jsAppendChild(E(_aU[1]),_aR);_aT=_aU[2];continue;}}}},_aW=function(_aX,_){while(1){var _aY=(function(_aZ,_){var _b0=E(_aZ);if(!_b0[0]){return _9;}else{var _b1=_b0[2],_b2=E(_b0[1]);if(!_b2[0]){var _b3=_b2[2],_b4=E(_b2[1]);switch(_b4[0]){case 0:var _b5=E(_aN),_b6=jsSet(_b5,_b4[1],_b3),_b7=_b1,_=_;while(1){var _b8=E(_b7);if(!_b8[0]){return _9;}else{var _b9=_b8[2],_ba=E(_b8[1]);if(!_ba[0]){var _bb=_ba[2],_bc=E(_ba[1]);switch(_bc[0]){case 0:var _bd=jsSet(_b5,_bc[1],_bb);_b7=_b9;continue;case 1:var _be=jsSetStyle(_b5,_bc[1],_bb);_b7=_b9;continue;default:var _bf=jsSetAttr(_b5,_bc[1],_bb);_b7=_b9;continue;}}else{var _bg=B(_aO(_ba[1],_));_b7=_b9;continue;}}}break;case 1:var _bh=E(_aN),_bi=jsSetStyle(_bh,_b4[1],_b3),_bj=_b1,_=_;while(1){var _bk=E(_bj);if(!_bk[0]){return _9;}else{var _bl=_bk[2],_bm=E(_bk[1]);if(!_bm[0]){var _bn=_bm[2],_bo=E(_bm[1]);switch(_bo[0]){case 0:var _bp=jsSet(_bh,_bo[1],_bn);_bj=_bl;continue;case 1:var _bq=jsSetStyle(_bh,_bo[1],_bn);_bj=_bl;continue;default:var _br=jsSetAttr(_bh,_bo[1],_bn);_bj=_bl;continue;}}else{var _bs=B(_aO(_bm[1],_));_bj=_bl;continue;}}}break;default:var _bt=E(_aN),_bu=jsSetAttr(_bt,_b4[1],_b3),_bv=_b1,_=_;while(1){var _bw=E(_bv);if(!_bw[0]){return _9;}else{var _bx=_bw[2],_by=E(_bw[1]);if(!_by[0]){var _bz=_by[2],_bA=E(_by[1]);switch(_bA[0]){case 0:var _bB=jsSet(_bt,_bA[1],_bz);_bv=_bx;continue;case 1:var _bC=jsSetStyle(_bt,_bA[1],_bz);_bv=_bx;continue;default:var _bD=jsSetAttr(_bt,_bA[1],_bz);_bv=_bx;continue;}}else{var _bE=B(_aO(_by[1],_));_bv=_bx;continue;}}}}}else{var _bF=B(_aO(_b2[1],_));_aX=_b1;return null;}}})(_aX,_);if(_aY!=null){return _aY;}}},_bG=function(_){return new F(function(){return _aW(_aM,_);});};return new F(function(){return A(_1,[_aK,_bG]);});},_bH=function(_bI,_bJ,_bK,_bL){var _bM=B(_ay(_bJ)),_bN=function(_bO){var _bP=new T(function(){return B(A(_aE,[_bM,_bO]));}),_bQ=new T(function(){return B(_aI(_bI,_bJ,_bO,_bL));});return new F(function(){return A(_aA,[_bM,_bQ,_bP]);});};return new F(function(){return A(_aC,[_bM,_bK,_bN]);});},_bR=function(_bS,_){var _bT=E(_bS);if(!_bT[0]){return _3y;}else{var _bU=B(A(_au,[_7e,_bT[1],_])),_bV=B(A(_bH,[_U,_7e,_at,[1,[1,[1,_bU,_3y]],_3y],_])),_bW=B(_bR(_bT[2],_));return [1,_bV,_bW];}},_bX=function(_bY,_bZ,_){var _c0=B(A(_au,[_7e,_bY,_])),_c1=B(A(_bH,[_U,_7e,_at,[1,[1,[1,_c0,_3y]],_3y],_])),_c2=B(_bR(_bZ,_));return [1,_c1,_c2];},_c3=function(_){return new F(function(){return jsCreateElem("td");});},_c4=function(_c5,_){var _c6=E(_c5);if(!_c6[0]){return _3y;}else{var _c7=B(A(_bH,[_U,_7e,_c3,[1,[1,[1,_c6[1],_3y]],_3y],_])),_c8=B(_c4(_c6[2],_));return [1,_c7,_c8];}},_c9=function(_ca,_cb,_){var _cc=B(A(_bH,[_U,_7e,_c3,[1,[1,[1,_ca,_3y]],_3y],_])),_cd=B(_c4(_cb,_));return [1,_cc,_cd];},_ce=function(_cf,_){var _cg=jsShow(_cf),_ch=jsCreateTextNode(toJSStr(fromJSStr(_cg)));return new F(function(){return A(_bH,[_U,_7e,_c3,[1,[1,[1,_ch,_3y]],_3y],_]);});},_ci=function(_cj,_ck){var _cl=(_ck-_cj)*25/900;if(!_cl){var _cm=rintDouble(0);return _cm&4294967295;}else{if(_cl<=0){var _cn=rintDouble( -_cl/0.1);return _cn&4294967295;}else{var _co=rintDouble(_cl/0.1);return _co&4294967295;}}},_cp=function(_cq,_cr){return [0,E(_cq),toJSStr(E(_cr))];},_cs=2,_ct=0,_cu=function(_){return new F(function(){return jsCreateElem("input");});},_cv=new T(function(){return B(unCStr("x1"));}),_cw=function(_){return new F(function(){return jsCreateElem("tr");});},_cx=new T(function(){return B(unCStr("y1"));}),_cy=new T(function(){return B(unCStr("x2"));}),_cz=new T(function(){return B(unCStr("y2"));}),_cA=new T(function(){return B(unCStr("frames"));}),_cB=new T(function(){return B(unCStr("time (minutes)"));}),_cC=new T(function(){return B(unCStr("title"));}),_cD=new T(function(){return B(unCStr("Delete"));}),_cE=[1,_cD,_3y],_cF=[1,_cC,_cE],_cG=[1,_cB,_cF],_cH=[1,_cA,_cG],_cI=[1,_cz,_cH],_cJ=[1,_cy,_cI],_cK=[1,_cx,_cJ],_cL=function(_){return new F(function(){return jsCreateElem("span");});},_cM=new T(function(){return [0,[2,"class"],"glyphicon glyphicon-remove"];}),_cN=[1,_cM,_3y],_cO=new T(function(){return B(_bH(_U,_7e,_cL,_cN));}),_cP=function(_){return new F(function(){return jsCreateElem("button");});},_cQ=function(_cR){var _cS=I_decodeDouble(_cR);return [0,[1,_cS[2]],_cS[1]];},_cT=function(_cU){var _cV=E(_cU);if(!_cV[0]){return _cV[1];}else{return new F(function(){return I_toNumber(_cV[1]);});}},_cW=function(_cX){return [0,_cX];},_cY=function(_cZ){var _d0=hs_intToInt64(2147483647),_d1=hs_leInt64(_cZ,_d0);if(!_d1){return [1,I_fromInt64(_cZ)];}else{var _d2=hs_intToInt64(-2147483648),_d3=hs_geInt64(_cZ,_d2);if(!_d3){return [1,I_fromInt64(_cZ)];}else{var _d4=hs_int64ToInt(_cZ);return new F(function(){return _cW(_d4);});}}},_d5=function(_d6){var _d7=hs_intToInt64(_d6);return E(_d7);},_d8=function(_d9){var _da=E(_d9);if(!_da[0]){return new F(function(){return _d5(_da[1]);});}else{return new F(function(){return I_toInt64(_da[1]);});}},_db=new T(function(){return [2,"value"];}),_dc=new T(function(){return [0,[2,"type"],"text"];}),_dd=new T(function(){return [0,[2,"class"],"btn btn-danger"];}),_de=function(_df){return E(E(_df)[1]);},_dg=function(_dh){return E(E(_dh)[2]);},_di=function(_dj){return E(E(_dj)[1]);},_dk=function(_){return new F(function(){return nMV(_75);});},_dl=new T(function(){return B(_9R(_dk));}),_dm=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_dn=function(_do){return E(E(_do)[2]);},_dp=function(_dq,_dr,_ds,_dt,_du,_dv){var _dw=B(_de(_dq)),_dx=B(_ay(_dw)),_dy=new T(function(){return B(_1(_dw));}),_dz=new T(function(){return B(_aE(_dx));}),_dA=new T(function(){return B(A(_aG,[_dr,_dt]));}),_dB=new T(function(){return B(A(_di,[_ds,_du]));}),_dC=function(_dD){return new F(function(){return A(_dz,[[0,_dB,_dA,_dD]]);});},_dE=function(_dF){var _dG=new T(function(){var _dH=new T(function(){var _dI=E(_dA),_dJ=E(_dB),_dK=E(_dF),_dL=function(_dM,_){var _dN=B(A(_dK,[_dM,_]));return _9V;},_dO=__createJSFunc(2,E(_dL)),_dP=_dO,_dQ=function(_){return new F(function(){return E(_dm)(_dI,_dJ,_dP);});};return E(_dQ);});return B(A(_dy,[_dH]));});return new F(function(){return A(_aC,[_dx,_dG,_dC]);});},_dR=new T(function(){var _dS=new T(function(){return B(_1(_dw));}),_dT=function(_dU){var _dV=new T(function(){var _dW=function(_){var _=wMV(E(_dl),[1,_dU]);return new F(function(){return A(_dg,[_ds,_du,_dU,_]);});};return B(A(_dS,[_dW]));});return new F(function(){return A(_aC,[_dx,_dV,_dv]);});};return B(A(_dn,[_dq,_dT]));});return new F(function(){return A(_aC,[_dx,_dR,_dE]);});},_dX=function(_dY,_dZ){while(1){var _e0=E(_dY);if(!_e0[0]){return E(_dZ);}else{_dY=_e0[2];var _e1=[1,_e0[1],_dZ];_dZ=_e1;continue;}}},_e2=function(_e3,_e4){while(1){var _e5=E(_e3);if(!_e5[0]){_e3=[1,I_fromInt(_e5[1])];continue;}else{return [1,I_shiftLeft(_e5[1],_e4)];}}},_e6=function(_e7,_e8,_e9,_ea,_){var _eb=jsClearChildren(_ea),_ec=B(_bX(_cv,_cK,_)),_ed=_ec,_ee=new T(function(){return B(_8L(_ed));}),_ef=B(A(_bH,[_U,_7e,_cw,[1,_ee,_3y],_])),_eg=jsAppendChild(E(_ef),_ea),_eh=function(_ei,_){var _ej=E(_ei);if(!_ej[0]){return _3y;}else{var _ek=_ej[2],_el=E(_ej[1]),_em=_el[3],_en=E(_el[1]),_eo=E(_el[2]),_ep=E(_en[1]),_eq=B(_ce(_ep*25/900,_)),_er=_eq,_es=E(_en[2]),_et=B(_ce(_es*25/900,_)),_eu=_et,_ev=E(_eo[1]),_ew=B(_ce(_ev*25/900,_)),_ex=_ew,_ey=E(_eo[2]),_ez=B(_ce(_ey*25/900,_)),_eA=_ez,_eB=function(_eC){var _eD=B(_ce(_eC,_)),_eE=_eD,_eF=function(_eG){var _eH=rintDouble(_eG*5.8333333333333334e-2),_eI=B(_cQ(_eH)),_eJ=_eI[1],_eK=_eI[2],_eL=function(_eM){var _eN=B(_ce(_eM,_)),_eO=B(_c9(_er,[1,_eu,[1,_ex,[1,_eA,[1,_eE,[1,_eN,_3y]]]]],_)),_eP=_eO,_eQ=new T(function(){return B(_8L(_eP));}),_eR=B(A(_bH,[_U,_7e,_cw,[1,_eQ,_3y],_])),_eS=new T(function(){return B(_cp(_db,_em));}),_eT=B(A(_bH,[_U,_7e,_cu,[1,_dc,[1,_eS,_3y]],_])),_eU=_eT,_eV=B(A(_cO,[_])),_eW=B(A(_bH,[_U,_7e,_cP,[1,_dd,[1,[1,[1,_eV,_3y]],_3y]],_])),_eX=B(A(_bH,[_U,_7e,_c3,[1,[1,[1,_eU,_3y]],_3y],_])),_eY=E(_eR),_eZ=jsAppendChild(E(_eX),_eY),_f0=E(_eW),_f1=jsAppendChild(_f0,_eY),_f2=new T(function(){return B(A(_e8,[_el]));}),_f3=function(_f4){return E(_f2);},_f5=B(A(_dp,[_7f,_U,_as,_f0,_ct,_f3,_])),_f6=new T(function(){return B(A(_e7,[_eU,_el]));}),_f7=function(_f8){return E(_f6);},_f9=B(A(_dp,[_7f,_U,_n,_eU,_cs,_f7,_])),_fa=jsAppendChild(_eY,_ea),_fb=B(_eh(_ek,_));return [1,_9,_fb];};if(_eK>=0){return new F(function(){return _eL(B(_cT(B(_e2(_eJ,_eK)))));});}else{var _fc=hs_uncheckedIShiftRA64(B(_d8(_eJ)), -_eK);return new F(function(){return _eL(B(_cT(B(_cY(_fc)))));});}};if(_ep!=_ev){return new F(function(){return _eF(B(_ci(_ep,_ev)));});}else{return new F(function(){return _eF(B(_ci(_es,_ey)));});}};if(_ep!=_ev){return new F(function(){return _eB(B(_ci(_ep,_ev)));});}else{return new F(function(){return _eB(B(_ci(_es,_ey)));});}}},_fd=B(_eh(B(_dX(E(_e9)[2],_3y)),_));return _9;},_fe=function(_ff,_fg,_fh,_fi,_){var _fj=jsPushState(_fi),_fk=jsScale(_fi,_ff,_fg),_fl=B(A(_fh,[_fi,_])),_fm=jsPopState(_fi);return _9;},_fn=function(_fo,_fp,_){var _fq=jsBeginPath(_fp),_fr=B(A(_fo,[_fp,_])),_fs=jsStroke(_fp);return _9;},_ft=",",_fu="[",_fv="]",_fw="{",_fx="}",_fy=":",_fz="\"",_fA="true",_fB="false",_fC="null",_fD=function(_fE){return new F(function(){return jsStringify(E(_fE));});},_fF=function(_fG){return new F(function(){return _fD(_fG);});},_fH=function(_fI,_fJ){var _fK=E(_fJ);switch(_fK[0]){case 0:var _fL=_fK[1],_fM=new T(function(){return jsShow(_fL);});return [0,_fM,_fI];case 1:var _fN=_fK[1],_fO=new T(function(){return jsStringify(_fN);});return [0,_fO,_fI];case 2:return (!E(_fK[1]))?[0,_fB,_fI]:[0,_fA,_fI];case 3:var _fP=E(_fK[1]);if(!_fP[0]){return [0,_fu,[1,_fv,_fI]];}else{var _fQ=_fP[1],_fR=_fP[2],_fS=new T(function(){var _fT=new T(function(){var _fU=[1,_fv,_fI],_fV=function(_fW){var _fX=E(_fW);if(!_fX[0]){return E(_fU);}else{var _fY=_fX[1],_fZ=_fX[2],_g0=new T(function(){var _g1=new T(function(){return B(_fV(_fZ));}),_g2=B(_fH(_g1,_fY));return [1,_g2[1],_g2[2]];});return [1,_ft,_g0];}};return B(_fV(_fR));}),_g3=B(_fH(_fT,_fQ));return [1,_g3[1],_g3[2]];});return [0,_fu,_fS];}break;case 4:var _g4=E(_fK[1]);if(!_g4[0]){return [0,_fw,[1,_fx,_fI]];}else{var _g5=_g4[2],_g6=E(_g4[1]),_g7=_g6[1],_g8=_g6[2],_g9=new T(function(){var _ga=new T(function(){var _gb=[1,_fx,_fI],_gc=function(_gd){var _ge=E(_gd);if(!_ge[0]){return E(_gb);}else{var _gf=_ge[2],_gg=E(_ge[1]),_gh=_gg[2],_gi=new T(function(){var _gj=new T(function(){return B(_gc(_gf));}),_gk=B(_fH(_gj,_gh));return [1,_gk[1],_gk[2]];});return [1,_ft,[1,_fz,[1,_gg[1],[1,_fz,[1,_fy,_gi]]]]];}};return B(_gc(_g5));}),_gl=B(_fH(_ga,_g8));return [1,_gl[1],_gl[2]];}),_gm=new T(function(){return B(_fF(_g7));});return [0,_fw,[1,_gm,[1,_fy,_g9]]];}break;default:return [0,_fC,_fI];}},_gn=new T(function(){return toJSStr(_3y);}),_go=function(_gp){var _gq=B(_fH(_3y,_gp)),_gr=jsCat([1,_gq[1],_gq[2]],E(_gn));return E(_gr);},_gs=function(_gt,_gu){return E(_gt)!=E(_gu);},_gv=function(_gw,_gx){return E(_gw)==E(_gx);},_gy=[0,_gv,_gs],_gz=function(_gA,_gB,_gC){while(1){var _gD=E(_gC);if(!_gD[0]){return false;}else{if(!B(A(_V,[_gA,_gB,_gD[1]]))){_gC=_gD[2];continue;}else{return true;}}}},_gE=32,_gF=function(_gG){while(1){var _gH=E(_gG);if(!_gH[0]){return false;}else{var _gI=E(_gH[1]);if(!_gI[0]){return true;}else{if(!B(_gz(_gy,_gE,_gI))){_gG=_gH[2];continue;}else{return true;}}}}},_gJ=function(_gK){return E(E(_gK)[3]);},_gL=function(_gM,_gN,_gO){var _gP=E(_gM);return (_gP[0]==0)?false:(!B(_gF(B(_1F(_gJ,_gP)))))?(!B(_2f(_gN,_3y)))?(!B(_gz(_gy,_gE,_gN)))?(E(_gO)[0]==0)?false:true:false:false:false;},_gQ=function(_gR,_gS){var _gT=function(_){return new F(function(){return jsFind(toJSStr(E(_gS)));});};return new F(function(){return A(_1,[_gR,_gT]);});},_gU=new T(function(){return encodeURIComponent;}),_gV=new T(function(){return B(unCStr("data:text/plain;charset=utf-8,"));}),_gW=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:190:3-9"));}),_gX=[0,_75,_76,_3y,_gW,_75,_75],_gY=new T(function(){return B(_73(_gX));}),_gZ=new T(function(){return B(unCStr("href"));}),_h0=function(_h1,_h2,_h3,_h4,_h5){var _h6=function(_){var _h7=jsSetAttr(B(A(_aG,[_h1,_h3])),toJSStr(E(_h4)),toJSStr(E(_h5)));return _9;};return new F(function(){return A(_1,[_h2,_h6]);});},_h8=function(_h9,_ha,_){var _hb=B(A(_gQ,[_7e,_h9,_])),_hc=E(_hb);if(!_hc[0]){return new F(function(){return die(_gY);});}else{var _hd=E(_gU)(toJSStr(_ha)),_he=_hd,_hf=new T(function(){var _hg=new T(function(){var _hh=String(_he);return fromJSStr(_hh);},1);return B(_18(_gV,_hg));});return new F(function(){return A(_h0,[_U,_7e,_hc[1],_gZ,_hf,_]);});}},_hi=function(_hj,_hk,_hl,_){var _hm=jsPushState(_hl),_hn=jsRotate(_hl,_hj),_ho=B(A(_hk,[_hl,_])),_hp=jsPopState(_hl);return _9;},_hq=function(_hr,_hs,_ht,_hu,_){var _hv=jsPushState(_hu),_hw=jsTranslate(_hu,_hr,_hs),_hx=B(A(_ht,[_hu,_])),_hy=jsPopState(_hu);return _9;},_hz=function(_hA,_hB){if(_hB<=0){var _hC=function(_hD){var _hE=function(_hF){var _hG=function(_hH){var _hI=function(_hJ){var _hK=isDoubleNegativeZero(_hB),_hL=_hK,_hM=function(_hN){var _hO=E(_hA);if(!_hO){return (_hB>=0)?(E(_hL)==0)?E(_hB):3.141592653589793:3.141592653589793;}else{var _hP=E(_hB);return (_hP==0)?E(_hO):_hP+_hO;}};if(!E(_hL)){return new F(function(){return _hM(_);});}else{var _hQ=E(_hA),_hR=isDoubleNegativeZero(_hQ);if(!E(_hR)){return new F(function(){return _hM(_);});}else{return  -B(_hz( -_hQ,_hB));}}};if(_hB>=0){return new F(function(){return _hI(_);});}else{var _hS=E(_hA),_hT=isDoubleNegativeZero(_hS);if(!E(_hT)){return new F(function(){return _hI(_);});}else{return  -B(_hz( -_hS,_hB));}}};if(_hB>0){return new F(function(){return _hG(_);});}else{var _hU=E(_hA);if(_hU>=0){return new F(function(){return _hG(_);});}else{return  -B(_hz( -_hU,_hB));}}};if(_hB>=0){return new F(function(){return _hE(_);});}else{var _hV=E(_hA);if(_hV<=0){return new F(function(){return _hE(_);});}else{return 3.141592653589793+Math.atan(_hV/_hB);}}};if(!E(_hB)){if(E(_hA)<=0){return new F(function(){return _hC(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _hC(_);});}}else{return new F(function(){return Math.atan(E(_hA)/_hB);});}},_hW=function(_hX,_hY){return E(_hX)-E(_hY);},_hZ=function(_i0,_i1,_i2,_i3,_i4,_i5,_i6,_i7){var _i8=new T(function(){return B(_hW(_i3,_i1));}),_i9=new T(function(){return B(_hW(_i5,_i3));}),_ia=new T(function(){return B(_hW(_i7,_i5));}),_ib=new T(function(){return B(_hW(_i1,_i7));});return new F(function(){return Math.atan((Math.tan(B(_hz(_i8,_i2-_i0))-1.5707963267948966)+Math.tan(B(_hz(_i9,_i4-_i2)))+Math.tan(B(_hz(_ia,_i6-_i4))+1.5707963267948966)+Math.tan(B(_hz(_ib,_i0-_i6))-3.141592653589793))/4);});},_ic=function(_id){return E(_id)/2;},_ie=function(_if,_ig,_ih,_){var _ii=E(_if);return new F(function(){return _hq(E(_ii[1]),E(_ii[2]),_ig,E(_ih),_);});},_ij=function(_ik,_il){var _im=new T(function(){var _in=E(_ik),_io=E(E(_il)[2]),_ip=E(_io[1]),_iq=E(_ip[1]),_ir=E(_ip[2]),_is=E(_io[2]),_it=E(_is[1]),_iu=E(_is[2]),_iv=E(_io[3]),_iw=E(_iv[1]),_ix=E(_iv[2]),_iy=E(_io[4]),_iz=E(_iy[1]),_iA=E(_iy[2]);return Math.sqrt(E(_in[1])*E(_in[2])/(0.5*(_iq*_iA+_iz*_ix+_iw*_ir-_iq*_ix-_iw*_iA-_iz*_ir)+0.5*(_iz*_ix+_iw*_iu+_it*_iA-_iz*_iu-_it*_ix-_iw*_iA)));}),_iB=new T(function(){var _iC=E(_ik),_iD=_iC[1],_iE=_iC[2],_iF=new T(function(){return B(_ic(_iE));}),_iG=new T(function(){return B(_ic(_iD));});return [0,_iG,_iF];}),_iH=new T(function(){var _iI=E(E(_il)[2]),_iJ=E(_iI[1]),_iK=E(_iI[2]),_iL=E(_iI[3]),_iM=E(_iI[4]);return  -B(_hZ(E(_iJ[1]),_iJ[2],E(_iK[1]),_iK[2],E(_iL[1]),_iL[2],E(_iM[1]),_iM[2]));}),_iN=new T(function(){var _iO=E(E(_il)[2]),_iP=E(_iO[1]),_iQ=_iP[1],_iR=_iP[2],_iS=E(_iO[2]),_iT=_iS[1],_iU=_iS[2],_iV=E(_iO[3]),_iW=_iV[1],_iX=_iV[2],_iY=E(_iO[4]),_iZ=_iY[1],_j0=_iY[2],_j1=new T(function(){return (E(_iR)+E(_iU)+E(_iX)+E(_j0))/4/(-1);}),_j2=new T(function(){return (E(_iQ)+E(_iT)+E(_iW)+E(_iZ))/4/(-1);});return [0,_j2,_j1];}),_j3=function(_j4,_j5,_){var _j6=E(_iB),_j7=function(_j8,_){var _j9=E(_im),_ja=function(_jb,_){var _jc=function(_jd,_){return new F(function(){return _ie(_iN,_j4,_jd,_);});};return new F(function(){return _hi(E(_iH),_jc,E(_jb),_);});};return new F(function(){return _fe(_j9,_j9,_ja,E(_j8),_);});};return new F(function(){return _hq(E(_j6[1]),E(_j6[2]),_j7,E(_j5),_);});};return E(_j3);},_je=function(_jf,_jg,_){var _jh=E(_jf);if(!_jh[0]){return _9;}else{var _ji=E(_jh[1]),_jj=E(_jg),_jk=jsMoveTo(_jj,E(_ji[1]),E(_ji[2])),_jl=_jh[2],_=_;while(1){var _jm=E(_jl);if(!_jm[0]){return _9;}else{var _jn=E(_jm[1]),_jo=jsLineTo(_jj,E(_jn[1]),E(_jn[2]));_jl=_jm[2];continue;}}}},_jp=function(_jq,_jr,_){var _js=new T(function(){return E(E(_jq)[2]);}),_jt=new T(function(){return E(E(_js)[1]);}),_ju=new T(function(){return E(E(_js)[4]);}),_jv=new T(function(){return E(E(_js)[3]);}),_jw=new T(function(){return E(E(_js)[2]);});return new F(function(){return _je([1,_jt,[1,_jw,[1,_jv,[1,_ju,[1,_jt,_3y]]]]],_jr,_);});},_jx=",",_jy="rgba(",_jz=new T(function(){return toJSStr(_3y);}),_jA="rgb(",_jB=")",_jC=[1,_jB,_3y],_jD=function(_jE){var _jF=E(_jE);if(!_jF[0]){var _jG=_jF[1],_jH=_jF[2],_jI=_jF[3],_jJ=new T(function(){return String(_jI);}),_jK=new T(function(){return String(_jH);}),_jL=new T(function(){return String(_jG);}),_jM=jsCat([1,_jA,[1,_jL,[1,_jx,[1,_jK,[1,_jx,[1,_jJ,_jC]]]]]],E(_jz));return E(_jM);}else{var _jN=_jF[4],_jO=_jF[1],_jP=_jF[2],_jQ=_jF[3],_jR=new T(function(){return String(_jN);}),_jS=new T(function(){return String(_jQ);}),_jT=new T(function(){return String(_jP);}),_jU=new T(function(){return String(_jO);}),_jV=jsCat([1,_jy,[1,_jU,[1,_jx,[1,_jT,[1,_jx,[1,_jS,[1,_jx,[1,_jR,_jC]]]]]]]],E(_jz));return E(_jV);}},_jW="strokeStyle",_jX="fillStyle",_jY=function(_jZ,_k0){var _k1=new T(function(){return B(_jD(_jZ));}),_k2=function(_k3,_){var _k4=E(_k3),_k5=E(_jX),_k6=jsGet(_k4,_k5),_k7=E(_jW),_k8=jsGet(_k4,_k7),_k9=E(_k1),_ka=jsSet(_k4,_k5,_k9),_kb=jsSet(_k4,_k7,_k9),_kc=B(A(_k0,[_k4,_])),_kd=jsSet(_k4,_k5,_k6),_ke=jsSet(_k4,_k7,_k8);return _9;};return E(_k2);},_kf=function(_kg,_kh,_ki){var _kj=E(_ki);if(!_kj[0]){return [0];}else{var _kk=_kj[1],_kl=_kj[2];if(!B(A(_kg,[_kh,_kk]))){var _km=new T(function(){return B(_kf(_kg,_kh,_kl));});return [1,_kk,_km];}else{return E(_kl);}}},_kn=function(_ko){return E(E(_ko)[3]);},_kp="lineWidth",_kq=function(_kr,_ks){var _kt=new T(function(){return String(E(_kr));}),_ku=function(_kv,_){var _kw=E(_kv),_kx=E(_kp),_ky=jsGet(_kw,_kx),_kz=jsSet(_kw,_kx,E(_kt)),_kA=B(A(_ks,[_kw,_])),_kB=jsSet(_kw,_kx,_ky);return _9;};return E(_ku);},_kC=new T(function(){return B(unCStr("saveLink"));}),_kD=new T(function(){return B(unCStr("exportLink"));}),_kE=[0,255,0,255],_kF=1,_kG=900,_kH=[0,_kG,_kG],_kI=new T(function(){return B(unCStr("btn btn-primary"));}),_kJ=new T(function(){return B(unCStr("class"));}),_kK=new T(function(){return B(unCStr("btn btn-primary disabled"));}),_kL=new T(function(){return B(unCStr("value"));}),_kM=function(_kN,_){var _kO=jsHasCtx2D(_kN);if(!E(_kO)){return _75;}else{var _kP=jsGetCtx2D(_kN);return [1,[0,_kP,_kN]];}},_kQ=function(_kR,_){return new F(function(){return _kM(E(_kR),_);});},_kS=function(_kT,_kU){var _kV=function(_){var _kW=jsFind(toJSStr(E(_kU)));if(!_kW[0]){return _75;}else{return new F(function(){return _kQ(_kW[1],_);});}};return new F(function(){return A(_1,[_kT,_kV]);});},_kX=new T(function(){return B(unCStr("aligned"));}),_kY=new T(function(){return B(_kS(_7e,_kX));}),_kZ=new T(function(){return B(unCStr("original"));}),_l0=new T(function(){return B(_kS(_7e,_kZ));}),_l1=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:168:3-8"));}),_l2=[0,_75,_76,_3y,_l1,_75,_75],_l3=new T(function(){return B(_73(_l2));}),_l4=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:150:3-14"));}),_l5=[0,_75,_76,_3y,_l4,_75,_75],_l6=new T(function(){return B(_73(_l5));}),_l7=new T(function(){return B(unCStr("runfile"));}),_l8=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:149:3-10"));}),_l9=[0,_75,_76,_3y,_l8,_75,_75],_la=new T(function(){return B(_73(_l9));}),_lb=new T(function(){return B(unCStr("scans"));}),_lc=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:148:3-11"));}),_ld=[0,_75,_76,_3y,_lc,_75,_75],_le=new T(function(){return B(_73(_ld));}),_lf=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:147:3-11"));}),_lg=[0,_75,_76,_3y,_lf,_75,_75],_lh=new T(function(){return B(_73(_lg));}),_li=function(_lj,_lk,_){while(1){var _ll=E(_lj);if(!_ll[0]){return _9;}else{var _lm=E(_ll[1]),_ln=B(_je([1,_lm[1],[1,_lm[2],_3y]],_lk,_));_lj=_ll[2];continue;}}},_lo=[0,255,0,255],_lp=1,_lq=function(_lr){var _ls=new T(function(){var _lt=new T(function(){var _lu=E(_lr)[2];return function(_lv,_lw){return new F(function(){return _li(_lu,_lv,_lw);});};}),_lx=function(_ly,_){return new F(function(){return _fn(_lt,E(_ly),_);});};return B(_jY(_lo,_lx));});return new F(function(){return _kq(_lp,_ls);});},_lz=function(_lA,_lB,_lC,_lD,_lE){var _lF=function(_){var _lG=jsSet(B(A(_aG,[_lA,_lC])),toJSStr(E(_lD)),toJSStr(E(_lE)));return _9;};return new F(function(){return A(_1,[_lB,_lF]);});},_lH=function(_lI){while(1){var _lJ=E(_lI);if(!_lJ[0]){_lI=[1,I_fromInt(_lJ[1])];continue;}else{return new F(function(){return I_toString(_lJ[1]);});}}},_lK=function(_lL,_lM){return new F(function(){return _18(fromJSStr(B(_lH(_lL))),_lM);});},_lN=function(_lO,_lP){var _lQ=E(_lO);if(!_lQ[0]){var _lR=_lQ[1],_lS=E(_lP);return (_lS[0]==0)?_lR<_lS[1]:I_compareInt(_lS[1],_lR)>0;}else{var _lT=_lQ[1],_lU=E(_lP);return (_lU[0]==0)?I_compareInt(_lT,_lU[1])<0:I_compare(_lT,_lU[1])<0;}},_lV=[0,0],_lW=function(_lX,_lY,_lZ){if(_lX<=6){return new F(function(){return _lK(_lY,_lZ);});}else{if(!B(_lN(_lY,_lV))){return new F(function(){return _lK(_lY,_lZ);});}else{var _m0=new T(function(){return B(_18(fromJSStr(B(_lH(_lY))),[1,_8U,_lZ]));});return [1,_8V,_m0];}}},_m1=0,_m2=1,_m3=function(_m4){var _m5=E(_m4);if(!_m5[0]){return [0];}else{var _m6=_m5[2],_m7=new T(function(){return B(_m3(_m6));},1);return new F(function(){return _18(_m5[1],_m7);});}},_m8=new T(function(){return B(unCStr("\r\n"));}),_m9=new T(function(){return B(_18(_m8,_m8));}),_ma=function(_mb,_mc){var _md=E(_mc);if(!_md[0]){return [0];}else{var _me=_md[2],_mf=new T(function(){return B(_ma(_mb,_me));});return [1,_mb,[1,_md[1],_mf]];}},_mg=new T(function(){return B(unAppCStr("}",_m8));}),_mh=new T(function(){return B(_18(_m8,_mg));}),_mi=new T(function(){return B(unCStr("1"));}),_mj=new T(function(){return B(_18(_mi,_3y));}),_mk=[1,_gE,_mj],_ml=new T(function(){var _mm=jsShow(1);return B(_18(fromJSStr(_mm),_mk));}),_mn=[1,_gE,_ml],_mo=new T(function(){var _mp=jsShow(0);return fromJSStr(_mp);}),_mq=new T(function(){var _mr=jsShow(0.1);return fromJSStr(_mr);}),_ms=new T(function(){return B(unCStr("ccdtrans sav"));}),_mt=new T(function(){return B(unCStr("  ccdacq"));}),_mu=function(_mv,_mw,_mx,_my){if(!E(_mv)){var _mz=new T(function(){var _mA=E(_mx),_mB=_mA[2],_mC=_mA[3],_mD=E(_mA[1]),_mE=_mD[1],_mF=_mD[2],_mG=E(_mw),_mH=_mG[6],_mI=function(_mJ){var _mK=jsShow(_mJ),_mL=new T(function(){var _mM=new T(function(){var _mN=new T(function(){var _mO=E(_mE),_mP=E(_mB),_mQ=E(_mP[1]),_mR=function(_mS){var _mT=new T(function(){var _mU=new T(function(){var _mV=new T(function(){var _mW=new T(function(){var _mX=new T(function(){var _mY=new T(function(){var _mZ=E(_mH),_n0=E(_my),_n1=_mZ+12.5+(_mO*25/900-12.5)*Math.cos(_n0),_n2=jsShow(_n1),_n3=new T(function(){var _n4=new T(function(){var _n5=jsShow((_mZ+12.5+(_mQ*25/900-12.5)*Math.cos(_n0)-_n1)/_mS),_n6=new T(function(){var _n7=new T(function(){var _n8=(_mO*25/900-12.5)*Math.sin(_n0),_n9=jsShow(_n8),_na=new T(function(){var _nb=new T(function(){var _nc=jsShow(((_mQ*25/900-12.5)*Math.sin(_n0)-_n8)/_mS),_nd=new T(function(){var _ne=new T(function(){var _nf=new T(function(){var _ng=new T(function(){var _nh=new T(function(){return B(_18(_mC,_3y));});return B(_18(_mq,[1,_gE,_nh]));});return B(_18(B(_18(_mt,[1,_gE,_ng])),_mh));},1);return B(_18(_m8,_nf));});return B(unAppCStr(")",_ne));},1);return B(_18(fromJSStr(_nc),_nd));});return B(unAppCStr("+i*",_nb));},1);return B(_18(fromJSStr(_n9),_na));});return B(unAppCStr(") tmp1 (",_n7));},1);return B(_18(fromJSStr(_n5),_n6));});return B(unAppCStr("+i*",_n4));},1);return B(_18(fromJSStr(_n2),_n3));});return B(unAppCStr("  umv sah (",_mY));},1);return B(_18(_m8,_mX));});return B(unAppCStr("{",_mW));},1);return B(_18(_m8,_mV));});return B(unAppCStr(";i+=1)",_mU));},1);return new F(function(){return _18(B(_8W(0,_mS,_3y)),_mT);});};if(_mO!=_mQ){return B(_mR(B(_ci(_mO,_mQ))));}else{return B(_mR(B(_ci(E(_mF),E(_mP[2])))));}});return B(unAppCStr("for(i=0;i<=",_mN));},1);return B(_18(_m8,_mM));},1);return new F(function(){return _18(fromJSStr(_mK),_mL);});};if(!E(_mG[7])){return B(_mI(E(_mG[4])+E(_mF)*25/900));}else{return B(_mI(E(_mG[5])+E(_mF)*25/900));}});return new F(function(){return unAppCStr("umv sav ",_mz);});}else{var _ni=new T(function(){var _nj=E(_mx),_nk=_nj[2],_nl=_nj[3],_nm=E(_nj[1]),_nn=_nm[2],_no=E(_mw),_np=_no[4],_nq=_no[5],_nr=_no[7],_ns=E(_nm[1]),_nt=E(_my),_nu=jsShow(E(_no[6])+12.5+(_ns*25/900-12.5)*Math.cos(_nt)),_nv=new T(function(){var _nw=new T(function(){var _nx=jsShow((_ns*25/900-12.5)*Math.sin(_nt)),_ny=new T(function(){var _nz=new T(function(){var _nA=new T(function(){var _nB=new T(function(){var _nC=E(_nk),_nD=_nC[1],_nE=_nC[2],_nF=new T(function(){var _nG=new T(function(){var _nH=E(_nD),_nI=function(_nJ){var _nK=new T(function(){var _nL=new T(function(){return B(_18(_nl,_mn));});return B(_18(_mo,[1,_gE,_nL]));});return new F(function(){return _18(B(_8W(0,_nJ,_3y)),[1,_gE,_nK]);});};if(_ns!=_nH){return B(_nI(B(_ci(_ns,_nH))));}else{return B(_nI(B(_ci(E(_nn),E(_nE)))));}});return B(_18(_mq,[1,_gE,_nG]));});if(!E(_nr)){var _nM=jsShow(E(_np)+E(_nE)*25/900);return B(_18(fromJSStr(_nM),[1,_gE,_nF]));}else{var _nN=jsShow(E(_nq)+E(_nE)*25/900);return B(_18(fromJSStr(_nN),[1,_gE,_nF]));}});if(!E(_nr)){var _nO=jsShow(E(_np)+E(_nn)*25/900);return B(_18(fromJSStr(_nO),[1,_gE,_nB]));}else{var _nP=jsShow(E(_nq)+E(_nn)*25/900);return B(_18(fromJSStr(_nP),[1,_gE,_nB]));}});return B(_18(_ms,[1,_gE,_nA]));},1);return B(_18(_m8,_nz));},1);return B(_18(fromJSStr(_nx),_ny));});return B(unAppCStr(" tmp1 ",_nw));},1);return B(_18(fromJSStr(_nu),_nv));});return new F(function(){return unAppCStr("umv sah ",_ni);});}},_nQ=function(_nR){var _nS=new T(function(){var _nT=E(_nR),_nU=_nT[2],_nV=_nT[8],_nW=new T(function(){var _nX=new T(function(){var _nY=function(_nZ){var _o0=new T(function(){var _o1=E(_nZ),_o2=rintDouble(_o1*180/3.141592653589793),_o3=B(_cQ(_o2)),_o4=_o3[1],_o5=_o3[2],_o6=new T(function(){var _o7=new T(function(){var _o8=function(_o9){var _oa=E(_o9);if(E(E(_oa[1])[1])!=E(E(_oa[2])[1])){return new F(function(){return _mu(_m1,_nT,_oa,_o1);});}else{return new F(function(){return _mu(_m2,_nT,_oa,_o1);});}},_ob=B(_1F(_o8,B(_dX(_nU,_3y))));if(!_ob[0]){return [0];}else{var _oc=_ob[2],_od=new T(function(){return B(_ma(_m8,_oc));});return B(_m3([1,_ob[1],_od]));}},1);return B(_18(_m8,_o7));});if(_o5>=0){return B(_18(B(_lW(0,B(_e2(_o4,_o5)),_3y)),_o6));}else{var _oe=hs_uncheckedIShiftRA64(B(_d8(_o4)), -_o5);return B(_18(B(_lW(0,B(_cY(_oe)),_3y)),_o6));}});return new F(function(){return unAppCStr("umv sar ",_o0);});},_of=B(_1F(_nY,_nV));if(!_of[0]){return [0];}else{var _og=_of[2],_oh=new T(function(){return B(_ma(_m9,_og));});return B(_m3([1,_of[1],_oh]));}},1);return B(_18(_m8,_nX));},1);return B(_18(_nT[3],_nW));});return new F(function(){return unAppCStr("ccdnewfile ",_nS);});},_oi=function(_oj){return new F(function(){return fromJSStr(E(_oj));});},_ok=function(_ol,_om,_on,_oo){var _op=function(_){return new F(function(){return jsGet(B(A(_aG,[_ol,_on])),E(_oo));});};return new F(function(){return A(_1,[_om,_op]);});},_oq=function(_or,_os,_ot,_ou){var _ov=B(_ay(_os)),_ow=new T(function(){return B(_aE(_ov));}),_ox=function(_oy){var _oz=new T(function(){return B(_oi(_oy));});return new F(function(){return A(_ow,[_oz]);});},_oA=new T(function(){var _oB=new T(function(){return toJSStr(E(_ou));});return B(_ok(_or,_os,_ot,_oB));});return new F(function(){return A(_aC,[_ov,_oA,_ox]);});},_oC=new T(function(){return B(unCStr("value"));}),_oD=function(_oE,_oF,_oG){var _oH=E(_oG);if(!_oH[0]){return [0];}else{var _oI=_oH[1],_oJ=_oH[2];if(!B(A(_oE,[_oI]))){var _oK=new T(function(){return B(_oD(_oE,_oF,_oJ));});return [1,_oI,_oK];}else{var _oL=new T(function(){return B(_oD(_oE,_oF,_oJ));}),_oM=new T(function(){return B(A(_oF,[_oI]));});return [1,_oM,_oL];}}},_oN=function(_oO,_oP,_oQ,_oR,_){var _oS=B(A(_oq,[_U,_7e,_oQ,_oC,_])),_oT=_oS,_oU=E(_oP),_oV=rMV(_oU),_oW=E(_oV),_oX=_oW[2],_oY=new T(function(){var _oZ=function(_p0){var _p1=E(_p0);return [0,_p1[1],_p1[2],_oT];},_p2=function(_p3){return new F(function(){return _7r(_p3,_oR);});};return B(_oD(_p2,_oZ,_oX));}),_=wMV(_oU,[0,_oW[1],_oY,_oW[3],_oW[4],_oW[5],_oW[6],_oW[7],_oW[8]]);return new F(function(){return A(_oO,[_]);});},_p4=function(_p5,_p6,_p7,_){var _p8=rMV(_p6),_p9=_p8,_pa=E(_p5),_pb=_pa,_pc=rMV(_pb),_pd=_pc,_pe=B(A(_l0,[_])),_pf=E(_pe);if(!_pf[0]){return new F(function(){return die(_lh);});}else{var _pg=_pf[1],_ph=B(A(_kY,[_])),_pi=E(_ph);if(!_pi[0]){return new F(function(){return die(_le);});}else{var _pj=_pi[1],_pk=jsFind(toJSStr(E(_lb)));if(!_pk[0]){return new F(function(){return die(_la);});}else{var _pl=_pk[1],_pm=jsFind(toJSStr(E(_l7)));if(!_pm[0]){return new F(function(){return die(_l6);});}else{var _pn=new T(function(){return B(_kn(_pd));}),_po=B(A(_lz,[_U,_7e,_pm[1],_kL,_pn,_])),_pp=E(_kD),_pq=jsFind(toJSStr(_pp));if(!_pq[0]){return new F(function(){return die(_l3);});}else{var _pr=_pq[1],_ps=E(_pd),_pt=function(_){var _pu=function(_pv,_){var _pw=rMV(_pb),_px=E(_pw),_py=_px[2],_pz=new T(function(){return B(_kf(_7r,_pv,_py));}),_=wMV(_pb,[0,_px[1],_pz,_px[3],_px[4],_px[5],_px[6],_px[7],_px[8]]);return new F(function(){return _p4(_pa,_p6,_p7,_);});},_pA=function(_){return new F(function(){return _p4(_pa,_p6,_p7,_);});},_pB=function(_pC,_pD,_){return new F(function(){return _oN(_pA,_pa,_pC,_pD,_);});},_pE=B(_e6(_pB,_pu,_ps,E(_pl),_)),_pF=E(_p7),_pG=rMV(_pF),_pH=_pG,_pI=E(_pj),_pJ=jsResetCanvas(_pI[2]),_pK=_pI[1],_pL=function(_pM,_){var _pN=jsDrawImage(E(_pM),E(_pH),0,0);return _9;},_pO=function(_pP,_){return new F(function(){return _fe(0.3,0.3,_pL,E(_pP),_);});},_pQ=B(A(_ij,[_kH,_p9,_pO,_pK,_])),_pR=B(A(_lq,[_ps,_pK,_])),_pS=rMV(_pF),_pT=E(_pg),_pU=_pT[1],_pV=jsResetCanvas(_pT[2]),_pW=jsPushState(_pU),_pX=jsScale(_pU,0.3,0.3),_pY=jsDrawImage(_pU,E(_pS),0,0),_pZ=jsPopState(_pU),_q0=new T(function(){var _q1=function(_pD,_){return new F(function(){return _jp(_p9,_pD,_);});},_q2=function(_q3,_){return new F(function(){return _fn(_q1,E(_q3),_);});};return B(_jY(_kE,_q2));}),_q4=B(A(_kq,[_kF,_q0,_pU,_])),_q5=new T(function(){return B(_nQ(_ps));},1),_q6=B(_h8(_pp,_q5,_)),_q7=new T(function(){var _q8=new T(function(){return [4,E(B(_8B(_ps)))];}),_q9=new T(function(){return [4,E(B(_7X(_p9)))];});return fromJSStr(B(_go([4,E(B(_8t(_7B,[1,_q9,[1,_q8,_3y]])))])));},1);return new F(function(){return _h8(_kC,_q7,_);});};if(!B(_gL(_ps[2],_ps[3],_ps[8]))){var _qa=B(A(_h0,[_U,_7e,_pr,_kJ,_kK,_]));return new F(function(){return _pt(_);});}else{var _qb=B(A(_h0,[_U,_7e,_pr,_kJ,_kI,_]));return new F(function(){return _pt(_);});}}}}}}},_qc=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:101:3-9"));}),_qd=[0,_75,_76,_3y,_qc,_75,_75],_qe=new T(function(){return B(_73(_qd));}),_qf=function(_){return new F(function(){return die(_qe);});},_qg=2,_qh=function(_qi){return E(_qi)[2];},_qj=function(_){return _75;},_qk=function(_ql,_){return new F(function(){return _qj(_);});},_qm=[0,_qh,_qk],_qn=function(_qo,_qp){while(1){var _qq=E(_qo);if(!_qq[0]){return E(_qp);}else{var _qr=_qq[2],_qs=E(_qq[1]);if(_qp>_qs){_qo=_qr;_qp=_qs;continue;}else{_qo=_qr;continue;}}}},_qt=function(_qu,_qv,_qw){var _qx=E(_qu);if(_qw>_qx){return new F(function(){return _qn(_qv,_qx);});}else{return new F(function(){return _qn(_qv,_qw);});}},_qy=2,_qz=4,_qA=3,_qB=function(_qC,_qD){var _qE=function(_qF,_qG){while(1){var _qH=(function(_qI,_qJ){var _qK=E(_qI);if(!_qK[0]){return [0];}else{var _qL=_qK[2];if(!B(A(_qC,[_qK[1]]))){_qF=_qL;var _qM=_qJ+1|0;_qG=_qM;return null;}else{var _qN=new T(function(){return B(_qE(_qL,_qJ+1|0));});return [1,_qJ,_qN];}}})(_qF,_qG);if(_qH!=null){return _qH;}}},_qO=B(_qE(_qD,0));return (_qO[0]==0)?[0]:[1,_qO[1]];},_qP=function(_qQ){return E(_qQ);},_qR=function(_qS,_qT,_qU,_){var _qV=function(_qW,_){var _qX=E(_qS),_qY=rMV(_qX),_qZ=E(E(_qY)[2]),_r0=_qZ[1],_r1=_qZ[2],_r2=_qZ[3],_r3=_qZ[4],_r4=new T(function(){var _r5=new T(function(){var _r6=E(E(_qW)[1]),_r7=_r6[1],_r8=_r6[2],_r9=new T(function(){return B(_qP(_r8));}),_ra=new T(function(){return B(_qP(_r7));});return [0,_ra,_r9];}),_rb=new T(function(){var _rc=E(_r5),_rd=E(_r0);return Math.pow(E(_rc[1])-E(_rd[1]),2)+Math.pow(E(_rc[2])-E(_rd[2]),2);}),_re=new T(function(){var _rf=E(_r5),_rg=E(_r1);return Math.pow(E(_rf[1])-E(_rg[1]),2)+Math.pow(E(_rf[2])-E(_rg[2]),2);}),_rh=new T(function(){var _ri=E(_r5),_rj=E(_r2);return Math.pow(E(_ri[1])-E(_rj[1]),2)+Math.pow(E(_ri[2])-E(_rj[2]),2);}),_rk=new T(function(){var _rl=E(_r5),_rm=E(_r3);return Math.pow(E(_rl[1])-E(_rm[1]),2)+Math.pow(E(_rl[2])-E(_rm[2]),2);}),_rn=[1,_rh,[1,_rk,_3y]],_ro=new T(function(){return B(_qt(_re,_rn,E(_rb)));}),_rp=function(_rq){return E(_ro)==E(_rq);},_rr=B(_qB(_rp,[1,_rb,[1,_re,_rn]]));if(!_rr[0]){return 3;}else{switch(E(_rr[1])){case 0:return 0;break;case 1:return 2;break;case 3:return 1;break;default:return 3;}}}),_=wMV(_qX,[0,[1,_r4],_qZ]);return new F(function(){return A(_qU,[_]);});},_rs=B(A(_dp,[_7f,_qm,_as,_qT,_qy,_qV,_])),_rt=function(_ru,_){var _rv=E(_qS),_rw=rMV(_rv),_=wMV(_rv,[0,_1Z,E(_rw)[2]]);return new F(function(){return A(_qU,[_]);});},_rx=B(A(_dp,[_7f,_qm,_as,_qT,_qA,_rt,_])),_ry=function(_rz,_){var _rA=E(_qS),_rB=rMV(_rA),_rC=E(_rB),_rD=_rC[2],_rE=E(_rC[1]);if(!_rE[0]){var _rF=E(_rC);}else{var _rG=new T(function(){var _rH=E(E(_rz)[1]),_rI=_rH[1],_rJ=_rH[2],_rK=new T(function(){return B(_qP(_rJ));}),_rL=new T(function(){return B(_qP(_rI));});return [0,_rL,_rK];});switch(E(_rE[1])){case 0:var _rM=E(_rD),_rN=[0,_rE,[0,_rG,_rM[2],_rM[3],_rM[4]]];break;case 1:var _rO=E(_rD),_rN=[0,_rE,[0,_rO[1],_rO[2],_rO[3],_rG]];break;case 2:var _rP=E(_rD),_rN=[0,_rE,[0,_rP[1],_rG,_rP[3],_rP[4]]];break;default:var _rQ=E(_rD),_rN=[0,_rE,[0,_rQ[1],_rQ[2],_rG,_rQ[4]]];}var _rF=_rN;}var _=wMV(_rA,_rF);return new F(function(){return A(_qU,[_]);});},_rR=B(A(_dp,[_7f,_qm,_as,_qT,_qz,_ry,_]));return _9;},_rS=function(_rT,_rU,_rV,_rW,_rX,_rY,_rZ,_s0,_s1){if(!E(_rU)){return [0,_35,_rV,_rW,_rX,_rY,_rZ,_s0,_s1];}else{var _s2=E(_rV);if(!_s2[0]){return [0,_33,_3y,_rW,_rX,_rY,_rZ,_s0,_s1];}else{var _s3=_s2[1],_s4=new T(function(){return E(E(_s3)[1]);}),_s5=new T(function(){var _s6=E(_s4),_s7=_s6[1],_s8=E(E(_rT)[1]),_s9=_s8[1],_sa=E(_s6[2]),_sb=E(_s8[2]),_sc=_sb-_sa;if(!_sc){var _sd=E(_s7),_se=E(_s9),_sf=_se-_sd;if(!_sf){return [0,_se,_sa];}else{if(_sf<=0){if(0<= -_sf){return [0,_se,_sa];}else{return [0,_sd,_sb];}}else{if(0<=_sf){return [0,_se,_sa];}else{return [0,_sd,_sb];}}}}else{if(_sc<=0){var _sg=E(_s7),_sh=E(_s9),_si=_sh-_sg;if(!_si){if( -_sc<=0){return [0,_sh,_sa];}else{return [0,_sg,_sb];}}else{if(_si<=0){if( -_sc<= -_si){return [0,_sh,_sa];}else{return [0,_sg,_sb];}}else{if( -_sc<=_si){return [0,_sh,_sa];}else{return [0,_sg,_sb];}}}}else{var _sj=E(_s7),_sk=E(_s9),_sl=_sk-_sj;if(!_sl){return [0,_sj,_sb];}else{if(_sl<=0){if(_sc<= -_sl){return [0,_sk,_sa];}else{return [0,_sj,_sb];}}else{if(_sc<=_sl){return [0,_sk,_sa];}else{return [0,_sj,_sb];}}}}}});return [0,_33,[1,[0,_s4,_s5,_3y],_s2[2]],_rW,_rX,_rY,_rZ,_s0,_s1];}}},_sm=function(_sn,_so,_sp,_){var _sq=function(_sr,_){var _ss=E(_sn),_st=rMV(_ss),_su=E(_st),_sv=new T(function(){var _sw=E(E(_sr)[1]),_sx=_sw[1],_sy=_sw[2],_sz=new T(function(){return B(_qP(_sy));}),_sA=new T(function(){return B(_qP(_sx));});return [0,_sA,_sz];}),_=wMV(_ss,[0,_33,[1,[0,_sv,_sv,_3y],_su[2]],_su[3],_su[4],_su[5],_su[6],_su[7],_su[8]]);return new F(function(){return A(_sp,[_]);});},_sB=B(A(_dp,[_7f,_qm,_as,_so,_qy,_sq,_])),_sC=function(_sD,_){var _sE=E(_sn),_sF=rMV(_sE),_sG=E(_sF),_sH=B(_rS(_sD,_sG[1],_sG[2],_sG[3],_sG[4],_sG[5],_sG[6],_sG[7],_sG[8])),_=wMV(_sE,[0,_35,_sH[2],_sH[3],_sH[4],_sH[5],_sH[6],_sH[7],_sH[8]]);return new F(function(){return A(_sp,[_]);});},_sI=B(A(_dp,[_7f,_qm,_as,_so,_qA,_sC,_])),_sJ=function(_sK,_){var _sL=E(_sn),_sM=rMV(_sL),_sN=E(_sM),_sO=B(_rS(_sK,_sN[1],_sN[2],_sN[3],_sN[4],_sN[5],_sN[6],_sN[7],_sN[8])),_=wMV(_sL,[0,_sO[1],_sO[2],_sO[3],_sO[4],_sO[5],_sO[6],_sO[7],_sO[8]]);return new F(function(){return A(_sp,[_]);});},_sP=B(A(_dp,[_7f,_qm,_as,_so,_qz,_sJ,_]));return _9;},_sQ=new T(function(){return document;}),_sR=(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);}),_sS=(function(x){return document.getElementById(x).value;}),_sT=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_sU=new T(function(){return B(err(_sT));}),_sV=0,_sW=[0,_sV,_sV],_sX=1191,_sY=[0,_sX,_sV],_sZ=669,_t0=[0,_sX,_sZ],_t1=[0,_sV,_sZ],_t2=[0,_sW,_t1,_t0,_sY],_t3=[0,_1Z,_t2],_t4=90,_t5=[1,_t4,_3y],_t6=45,_t7=[1,_t6,_t5],_t8=0,_t9=[1,_t8,_t7],_ta=50,_tb=[0,_35,_3y,_3y,_t8,_ta,_t8,_2V,_t9],_tc=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_td=new T(function(){return B(err(_tc));}),_te=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_tf=new T(function(){return B(err(_te));}),_tg=new T(function(){return B(unCStr("Control.Exception.Base"));}),_th=new T(function(){return B(unCStr("base"));}),_ti=new T(function(){return B(unCStr("PatternMatchFail"));}),_tj=new T(function(){var _tk=hs_wordToWord64(18445595),_tl=hs_wordToWord64(52003073);return [0,_tk,_tl,[0,_tk,_tl,_th,_tg,_ti],_3y,_3y];}),_tm=function(_tn){return E(_tj);},_to=function(_tp){var _tq=E(_tp);return new F(function(){return _5p(B(_5n(_tq[1])),_tm,_tq[2]);});},_tr=function(_ts){return E(E(_ts)[1]);},_tt=function(_tu){return [0,_tv,_tu];},_tw=function(_tx,_ty){return new F(function(){return _18(E(_tx)[1],_ty);});},_tz=function(_tA,_tB){return new F(function(){return _6H(_tw,_tA,_tB);});},_tC=function(_tD,_tE,_tF){return new F(function(){return _18(E(_tE)[1],_tF);});},_tG=[0,_tC,_tr,_tz],_tv=new T(function(){return [0,_tm,_tG,_tt,_to,_tr];}),_tH=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_tI=function(_tJ){return E(E(_tJ)[3]);},_tK=function(_tL,_tM){var _tN=new T(function(){return B(A(_tI,[_tM,_tL]));});return new F(function(){return die(_tN);});},_tO=function(_tP,_tQ){return new F(function(){return _tK(_tP,_tQ);});},_tR=function(_tS,_tT){var _tU=E(_tT);if(!_tU[0]){return [0,_3y,_3y];}else{var _tV=_tU[1],_tW=_tU[2];if(!B(A(_tS,[_tV]))){return [0,_3y,_tU];}else{var _tX=new T(function(){var _tY=B(_tR(_tS,_tW));return [0,_tY[1],_tY[2]];}),_tZ=new T(function(){return E(E(_tX)[2]);}),_u0=new T(function(){return E(E(_tX)[1]);});return [0,[1,_tV,_u0],_tZ];}}},_u1=32,_u2=new T(function(){return B(unCStr("\n"));}),_u3=function(_u4){return (E(_u4)==124)?false:true;},_u5=function(_u6,_u7){var _u8=B(_tR(_u3,B(unCStr(_u6)))),_u9=_u8[1],_ua=function(_ub,_uc){var _ud=new T(function(){var _ue=new T(function(){var _uf=new T(function(){return B(_18(_uc,_u2));},1);return B(_18(_u7,_uf));});return B(unAppCStr(": ",_ue));},1);return new F(function(){return _18(_ub,_ud);});},_ug=E(_u8[2]);if(!_ug[0]){return new F(function(){return _ua(_u9,_3y);});}else{if(E(_ug[1])==124){return new F(function(){return _ua(_u9,[1,_u1,_ug[2]]);});}else{return new F(function(){return _ua(_u9,_3y);});}}},_uh=function(_ui){var _uj=new T(function(){return B(_u5(_ui,_tH));});return new F(function(){return _tO([0,_uj],_tv);});},_uk=new T(function(){return B(_uh("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_ul=function(_um,_un){while(1){var _uo=(function(_up,_uq){var _ur=E(_up);switch(_ur[0]){case 0:var _us=E(_uq);if(!_us[0]){return [0];}else{_um=B(A(_ur[1],[_us[1]]));_un=_us[2];return null;}break;case 1:var _ut=B(A(_ur[1],[_uq])),_uu=_uq;_um=_ut;_un=_uu;return null;case 2:return [0];case 3:var _uv=_ur[2],_uw=new T(function(){return B(_ul(_uv,_uq));});return [1,[0,_ur[1],_uq],_uw];default:return E(_ur[1]);}})(_um,_un);if(_uo!=null){return _uo;}}},_ux=function(_uy,_uz){var _uA=function(_uB){var _uC=E(_uz);if(_uC[0]==3){var _uD=_uC[2],_uE=new T(function(){return B(_ux(_uy,_uD));});return [3,_uC[1],_uE];}else{var _uF=E(_uy);if(_uF[0]==2){return E(_uC);}else{var _uG=E(_uC);if(_uG[0]==2){return E(_uF);}else{var _uH=function(_uI){var _uJ=E(_uG);if(_uJ[0]==4){var _uK=_uJ[1];return [1,function(_uL){return [4,new T(function(){return B(_18(B(_ul(_uF,_uL)),_uK));})];}];}else{var _uM=E(_uF);if(_uM[0]==1){var _uN=_uM[1],_uO=E(_uJ);if(!_uO[0]){return [1,function(_uP){return new F(function(){return _ux(B(A(_uN,[_uP])),_uO);});}];}else{var _uQ=_uO[1];return [1,function(_uR){var _uS=new T(function(){return B(A(_uQ,[_uR]));});return new F(function(){return _ux(B(A(_uN,[_uR])),_uS);});}];}}else{var _uT=E(_uJ);if(!_uT[0]){return E(_uk);}else{var _uU=_uT[1];return [1,function(_uV){var _uW=new T(function(){return B(A(_uU,[_uV]));});return new F(function(){return _ux(_uM,_uW);});}];}}}},_uX=E(_uF);switch(_uX[0]){case 1:var _uY=_uX[1],_uZ=E(_uG);if(_uZ[0]==4){var _v0=_uZ[1];return [1,function(_v1){return [4,new T(function(){return B(_18(B(_ul(B(A(_uY,[_v1])),_v1)),_v0));})];}];}else{return new F(function(){return _uH(_);});}break;case 4:var _v2=_uX[1],_v3=E(_uG);switch(_v3[0]){case 0:return [1,function(_v4){return [4,new T(function(){var _v5=new T(function(){return B(_ul(_v3,_v4));},1);return B(_18(_v2,_v5));})];}];case 1:var _v6=_v3[1];return [1,function(_v7){return [4,new T(function(){var _v8=new T(function(){return B(_ul(B(A(_v6,[_v7])),_v7));},1);return B(_18(_v2,_v8));})];}];default:var _v9=_v3[1];return [4,new T(function(){return B(_18(_v2,_v9));})];}break;default:return new F(function(){return _uH(_);});}}}}},_va=E(_uy);switch(_va[0]){case 0:var _vb=_va[1],_vc=E(_uz);if(!_vc[0]){var _vd=_vc[1];return [0,function(_ve){var _vf=new T(function(){return B(A(_vd,[_ve]));});return new F(function(){return _ux(B(A(_vb,[_ve])),_vf);});}];}else{return new F(function(){return _uA(_);});}break;case 3:var _vg=_va[2],_vh=new T(function(){return B(_ux(_vg,_uz));});return [3,_va[1],_vh];default:return new F(function(){return _uA(_);});}},_vi=new T(function(){return B(unCStr("("));}),_vj=new T(function(){return B(unCStr(")"));}),_vk=function(_vl,_vm){while(1){var _vn=E(_vl);if(!_vn[0]){return (E(_vm)[0]==0)?true:false;}else{var _vo=E(_vm);if(!_vo[0]){return false;}else{if(E(_vn[1])!=E(_vo[1])){return false;}else{_vl=_vn[2];_vm=_vo[2];continue;}}}}},_vp=function(_vq,_vr){return (!B(_vk(_vq,_vr)))?true:false;},_vs=[0,_vk,_vp],_vt=function(_vu,_vv){var _vw=E(_vu);switch(_vw[0]){case 0:var _vx=_vw[1];return [0,function(_vy){return new F(function(){return _vt(B(A(_vx,[_vy])),_vv);});}];case 1:var _vz=_vw[1];return [1,function(_vA){return new F(function(){return _vt(B(A(_vz,[_vA])),_vv);});}];case 2:return [2];case 3:var _vB=_vw[2],_vC=new T(function(){return B(_vt(_vB,_vv));});return new F(function(){return _ux(B(A(_vv,[_vw[1]])),_vC);});break;default:var _vD=function(_vE){var _vF=E(_vE);if(!_vF[0]){return [0];}else{var _vG=_vF[2],_vH=E(_vF[1]),_vI=new T(function(){return B(_vD(_vG));},1);return new F(function(){return _18(B(_ul(B(A(_vv,[_vH[1]])),_vH[2])),_vI);});}},_vJ=B(_vD(_vw[1]));return (_vJ[0]==0)?[2]:[4,_vJ];}},_vK=[2],_vL=function(_vM){return [3,_vM,_vK];},_vN=function(_vO,_vP){var _vQ=E(_vO);if(!_vQ){return new F(function(){return A(_vP,[_9]);});}else{var _vR=new T(function(){return B(_vN(_vQ-1|0,_vP));});return [0,function(_vS){return E(_vR);}];}},_vT=function(_vU,_vV,_vW){var _vX=new T(function(){return B(A(_vU,[_vL]));}),_vY=function(_vZ,_w0,_w1,_w2){while(1){var _w3=(function(_w4,_w5,_w6,_w7){var _w8=E(_w4);switch(_w8[0]){case 0:var _w9=E(_w5);if(!_w9[0]){return new F(function(){return A(_vV,[_w7]);});}else{_vZ=B(A(_w8[1],[_w9[1]]));_w0=_w9[2];var _wa=_w6+1|0,_wb=_w7;_w1=_wa;_w2=_wb;return null;}break;case 1:var _wc=B(A(_w8[1],[_w5])),_wd=_w5,_wa=_w6,_wb=_w7;_vZ=_wc;_w0=_wd;_w1=_wa;_w2=_wb;return null;case 2:return new F(function(){return A(_vV,[_w7]);});break;case 3:var _we=new T(function(){return B(_vt(_w8,_w7));}),_wf=function(_wg){return E(_we);};return new F(function(){return _vN(_w6,_wf);});break;default:return new F(function(){return _vt(_w8,_w7);});}})(_vZ,_w0,_w1,_w2);if(_w3!=null){return _w3;}}};return function(_wh){return new F(function(){return _vY(_vX,_wh,0,_vW);});};},_wi=function(_wj){return new F(function(){return A(_wj,[_3y]);});},_wk=function(_wl,_wm){var _wn=function(_wo){var _wp=E(_wo);if(!_wp[0]){return E(_wi);}else{var _wq=_wp[1],_wr=_wp[2];if(!B(A(_wl,[_wq]))){return E(_wi);}else{var _ws=new T(function(){return B(_wn(_wr));}),_wt=function(_wu){var _wv=new T(function(){var _ww=function(_wx){return new F(function(){return A(_wu,[[1,_wq,_wx]]);});};return B(A(_ws,[_ww]));});return [0,function(_wy){return E(_wv);}];};return E(_wt);}}};return function(_wz){return new F(function(){return A(_wn,[_wz,_wm]);});};},_wA=[6],_wB=new T(function(){return B(unCStr("valDig: Bad base"));}),_wC=new T(function(){return B(err(_wB));}),_wD=function(_wE,_wF){var _wG=function(_wH,_wI){var _wJ=E(_wH);if(!_wJ[0]){var _wK=new T(function(){return B(A(_wI,[_3y]));}),_wL=function(_wM){return new F(function(){return A(_wM,[_wK]);});};return E(_wL);}else{var _wN=_wJ[2],_wO=E(_wJ[1]),_wP=function(_wQ){var _wR=new T(function(){var _wS=function(_wT){return new F(function(){return A(_wI,[[1,_wQ,_wT]]);});};return B(_wG(_wN,_wS));}),_wU=function(_wV){var _wW=new T(function(){return B(A(_wR,[_wV]));});return [0,function(_wX){return E(_wW);}];};return E(_wU);};switch(E(_wE)){case 8:if(48>_wO){var _wY=new T(function(){return B(A(_wI,[_3y]));}),_wZ=function(_x0){return new F(function(){return A(_x0,[_wY]);});};return E(_wZ);}else{if(_wO>55){var _x1=new T(function(){return B(A(_wI,[_3y]));}),_x2=function(_x3){return new F(function(){return A(_x3,[_x1]);});};return E(_x2);}else{return new F(function(){return _wP(_wO-48|0);});}}break;case 10:if(48>_wO){var _x4=new T(function(){return B(A(_wI,[_3y]));}),_x5=function(_x6){return new F(function(){return A(_x6,[_x4]);});};return E(_x5);}else{if(_wO>57){var _x7=new T(function(){return B(A(_wI,[_3y]));}),_x8=function(_x9){return new F(function(){return A(_x9,[_x7]);});};return E(_x8);}else{return new F(function(){return _wP(_wO-48|0);});}}break;case 16:if(48>_wO){if(97>_wO){if(65>_wO){var _xa=new T(function(){return B(A(_wI,[_3y]));}),_xb=function(_xc){return new F(function(){return A(_xc,[_xa]);});};return E(_xb);}else{if(_wO>70){var _xd=new T(function(){return B(A(_wI,[_3y]));}),_xe=function(_xf){return new F(function(){return A(_xf,[_xd]);});};return E(_xe);}else{return new F(function(){return _wP((_wO-65|0)+10|0);});}}}else{if(_wO>102){if(65>_wO){var _xg=new T(function(){return B(A(_wI,[_3y]));}),_xh=function(_xi){return new F(function(){return A(_xi,[_xg]);});};return E(_xh);}else{if(_wO>70){var _xj=new T(function(){return B(A(_wI,[_3y]));}),_xk=function(_xl){return new F(function(){return A(_xl,[_xj]);});};return E(_xk);}else{return new F(function(){return _wP((_wO-65|0)+10|0);});}}}else{return new F(function(){return _wP((_wO-97|0)+10|0);});}}}else{if(_wO>57){if(97>_wO){if(65>_wO){var _xm=new T(function(){return B(A(_wI,[_3y]));}),_xn=function(_xo){return new F(function(){return A(_xo,[_xm]);});};return E(_xn);}else{if(_wO>70){var _xp=new T(function(){return B(A(_wI,[_3y]));}),_xq=function(_xr){return new F(function(){return A(_xr,[_xp]);});};return E(_xq);}else{return new F(function(){return _wP((_wO-65|0)+10|0);});}}}else{if(_wO>102){if(65>_wO){var _xs=new T(function(){return B(A(_wI,[_3y]));}),_xt=function(_xu){return new F(function(){return A(_xu,[_xs]);});};return E(_xt);}else{if(_wO>70){var _xv=new T(function(){return B(A(_wI,[_3y]));}),_xw=function(_xx){return new F(function(){return A(_xx,[_xv]);});};return E(_xw);}else{return new F(function(){return _wP((_wO-65|0)+10|0);});}}}else{return new F(function(){return _wP((_wO-97|0)+10|0);});}}}else{return new F(function(){return _wP(_wO-48|0);});}}break;default:return E(_wC);}}},_xy=function(_xz){var _xA=E(_xz);if(!_xA[0]){return [2];}else{return new F(function(){return A(_wF,[_xA]);});}};return function(_xB){return new F(function(){return A(_wG,[_xB,_S,_xy]);});};},_xC=16,_xD=8,_xE=function(_xF){var _xG=function(_xH){return new F(function(){return A(_xF,[[5,[0,_xD,_xH]]]);});},_xI=function(_xJ){return new F(function(){return A(_xF,[[5,[0,_xC,_xJ]]]);});},_xK=function(_xL){switch(E(_xL)){case 79:return [1,B(_wD(_xD,_xG))];case 88:return [1,B(_wD(_xC,_xI))];case 111:return [1,B(_wD(_xD,_xG))];case 120:return [1,B(_wD(_xC,_xI))];default:return [2];}},_xM=[0,_xK];return function(_xN){return (E(_xN)==48)?E(_xM):[2];};},_xO=function(_xP){return [0,B(_xE(_xP))];},_xQ=function(_xR){return new F(function(){return A(_xR,[_75]);});},_xS=function(_xT){return new F(function(){return A(_xT,[_75]);});},_xU=10,_xV=[0,1],_xW=[0,2147483647],_xX=function(_xY,_xZ){while(1){var _y0=E(_xY);if(!_y0[0]){var _y1=_y0[1],_y2=E(_xZ);if(!_y2[0]){var _y3=_y2[1],_y4=addC(_y1,_y3);if(!E(_y4[2])){return [0,_y4[1]];}else{_xY=[1,I_fromInt(_y1)];_xZ=[1,I_fromInt(_y3)];continue;}}else{_xY=[1,I_fromInt(_y1)];_xZ=_y2;continue;}}else{var _y5=E(_xZ);if(!_y5[0]){_xY=_y0;_xZ=[1,I_fromInt(_y5[1])];continue;}else{return [1,I_add(_y0[1],_y5[1])];}}}},_y6=new T(function(){return B(_xX(_xW,_xV));}),_y7=function(_y8){var _y9=E(_y8);if(!_y9[0]){var _ya=E(_y9[1]);return (_ya==(-2147483648))?E(_y6):[0, -_ya];}else{return [1,I_negate(_y9[1])];}},_yb=[0,10],_yc=function(_yd,_ye){while(1){var _yf=E(_yd);if(!_yf[0]){return E(_ye);}else{_yd=_yf[2];var _yg=_ye+1|0;_ye=_yg;continue;}}},_yh=function(_yi){return new F(function(){return _cW(E(_yi));});},_yj=new T(function(){return B(unCStr("this should not happen"));}),_yk=new T(function(){return B(err(_yj));}),_yl=function(_ym,_yn){while(1){var _yo=E(_ym);if(!_yo[0]){var _yp=_yo[1],_yq=E(_yn);if(!_yq[0]){var _yr=_yq[1];if(!(imul(_yp,_yr)|0)){return [0,imul(_yp,_yr)|0];}else{_ym=[1,I_fromInt(_yp)];_yn=[1,I_fromInt(_yr)];continue;}}else{_ym=[1,I_fromInt(_yp)];_yn=_yq;continue;}}else{var _ys=E(_yn);if(!_ys[0]){_ym=_yo;_yn=[1,I_fromInt(_ys[1])];continue;}else{return [1,I_mul(_yo[1],_ys[1])];}}}},_yt=function(_yu,_yv){var _yw=E(_yv);if(!_yw[0]){return [0];}else{var _yx=E(_yw[2]);if(!_yx[0]){return E(_yk);}else{var _yy=_yx[2],_yz=new T(function(){return B(_yt(_yu,_yy));});return [1,B(_xX(B(_yl(_yw[1],_yu)),_yx[1])),_yz];}}},_yA=[0,0],_yB=function(_yC,_yD,_yE){while(1){var _yF=(function(_yG,_yH,_yI){var _yJ=E(_yI);if(!_yJ[0]){return E(_yA);}else{if(!E(_yJ[2])[0]){return E(_yJ[1]);}else{var _yK=E(_yH);if(_yK<=40){var _yL=_yA,_yM=_yJ;while(1){var _yN=E(_yM);if(!_yN[0]){return E(_yL);}else{var _yO=B(_xX(B(_yl(_yL,_yG)),_yN[1]));_yM=_yN[2];_yL=_yO;continue;}}}else{var _yP=B(_yl(_yG,_yG));if(!(_yK%2)){_yC=_yP;_yD=quot(_yK+1|0,2);var _yQ=B(_yt(_yG,_yJ));_yE=_yQ;return null;}else{_yC=_yP;_yD=quot(_yK+1|0,2);var _yQ=B(_yt(_yG,[1,_yA,_yJ]));_yE=_yQ;return null;}}}}})(_yC,_yD,_yE);if(_yF!=null){return _yF;}}},_yR=function(_yS,_yT){var _yU=new T(function(){return B(_yc(_yT,0));},1);return new F(function(){return _yB(_yS,_yU,B(_1F(_yh,_yT)));});},_yV=function(_yW){var _yX=new T(function(){var _yY=new T(function(){var _yZ=function(_z0){var _z1=new T(function(){return B(_yR(_yb,_z0));});return new F(function(){return A(_yW,[[1,_z1]]);});};return [1,B(_wD(_xU,_yZ))];}),_z2=function(_z3){if(E(_z3)==43){var _z4=function(_z5){var _z6=new T(function(){return B(_yR(_yb,_z5));});return new F(function(){return A(_yW,[[1,_z6]]);});};return [1,B(_wD(_xU,_z4))];}else{return [2];}},_z7=function(_z8){if(E(_z8)==45){var _z9=function(_za){var _zb=new T(function(){return B(_y7(B(_yR(_yb,_za))));});return new F(function(){return A(_yW,[[1,_zb]]);});};return [1,B(_wD(_xU,_z9))];}else{return [2];}};return B(_ux(B(_ux([0,_z7],[0,_z2])),_yY));}),_zc=function(_zd){return (E(_zd)==69)?E(_yX):[2];},_ze=function(_zf){return (E(_zf)==101)?E(_yX):[2];};return new F(function(){return _ux([0,_ze],[0,_zc]);});},_zg=function(_zh){var _zi=function(_zj){return new F(function(){return A(_zh,[[1,_zj]]);});};return function(_zk){return (E(_zk)==46)?[1,B(_wD(_xU,_zi))]:[2];};},_zl=function(_zm){return [0,B(_zg(_zm))];},_zn=function(_zo){var _zp=function(_zq){var _zr=function(_zs){var _zt=function(_zu){return new F(function(){return A(_zo,[[5,[1,_zq,_zs,_zu]]]);});};return [1,B(_vT(_yV,_xQ,_zt))];};return [1,B(_vT(_zl,_xS,_zr))];};return new F(function(){return _wD(_xU,_zp);});},_zv=function(_zw){return [1,B(_zn(_zw))];},_zx=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_zy=function(_zz){return new F(function(){return _gz(_gy,_zz,_zx);});},_zA=false,_zB=true,_zC=function(_zD){var _zE=new T(function(){return B(A(_zD,[_xD]));}),_zF=new T(function(){return B(A(_zD,[_xC]));});return function(_zG){switch(E(_zG)){case 79:return E(_zE);case 88:return E(_zF);case 111:return E(_zE);case 120:return E(_zF);default:return [2];}};},_zH=function(_zI){return [0,B(_zC(_zI))];},_zJ=function(_zK){return new F(function(){return A(_zK,[_xU]);});},_zL=function(_zM){var _zN=new T(function(){return B(_8W(9,_zM,_3y));});return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",_zN)));});},_zO=function(_zP){var _zQ=E(_zP);if(!_zQ[0]){return E(_zQ[1]);}else{return new F(function(){return I_toInt(_zQ[1]);});}},_zR=function(_zS,_zT){var _zU=E(_zS);if(!_zU[0]){var _zV=_zU[1],_zW=E(_zT);return (_zW[0]==0)?_zV<=_zW[1]:I_compareInt(_zW[1],_zV)>=0;}else{var _zX=_zU[1],_zY=E(_zT);return (_zY[0]==0)?I_compareInt(_zX,_zY[1])<=0:I_compare(_zX,_zY[1])<=0;}},_zZ=function(_A0){return [2];},_A1=function(_A2){var _A3=E(_A2);if(!_A3[0]){return E(_zZ);}else{var _A4=_A3[1],_A5=E(_A3[2]);if(!_A5[0]){return E(_A4);}else{var _A6=new T(function(){return B(_A1(_A5));}),_A7=function(_A8){var _A9=new T(function(){return B(A(_A6,[_A8]));});return new F(function(){return _ux(B(A(_A4,[_A8])),_A9);});};return E(_A7);}}},_Aa=function(_Ab,_Ac){var _Ad=function(_Ae,_Af,_Ag){var _Ah=E(_Ae);if(!_Ah[0]){return new F(function(){return A(_Ag,[_Ab]);});}else{var _Ai=_Ah[2],_Aj=E(_Af);if(!_Aj[0]){return [2];}else{var _Ak=_Aj[2];if(E(_Ah[1])!=E(_Aj[1])){return [2];}else{var _Al=new T(function(){return B(_Ad(_Ai,_Ak,_Ag));});return [0,function(_Am){return E(_Al);}];}}}};return function(_An){return new F(function(){return _Ad(_Ab,_An,_Ac);});};},_Ao=new T(function(){return B(unCStr("SO"));}),_Ap=14,_Aq=function(_Ar){var _As=new T(function(){return B(A(_Ar,[_Ap]));}),_At=function(_Au){return E(_As);};return [1,B(_Aa(_Ao,_At))];},_Av=new T(function(){return B(unCStr("SOH"));}),_Aw=1,_Ax=function(_Ay){var _Az=new T(function(){return B(A(_Ay,[_Aw]));}),_AA=function(_AB){return E(_Az);};return [1,B(_Aa(_Av,_AA))];},_AC=function(_AD){return [1,B(_vT(_Ax,_Aq,_AD))];},_AE=new T(function(){return B(unCStr("NUL"));}),_AF=0,_AG=function(_AH){var _AI=new T(function(){return B(A(_AH,[_AF]));}),_AJ=function(_AK){return E(_AI);};return [1,B(_Aa(_AE,_AJ))];},_AL=new T(function(){return B(unCStr("STX"));}),_AM=2,_AN=function(_AO){var _AP=new T(function(){return B(A(_AO,[_AM]));}),_AQ=function(_AR){return E(_AP);};return [1,B(_Aa(_AL,_AQ))];},_AS=new T(function(){return B(unCStr("ETX"));}),_AT=3,_AU=function(_AV){var _AW=new T(function(){return B(A(_AV,[_AT]));}),_AX=function(_AY){return E(_AW);};return [1,B(_Aa(_AS,_AX))];},_AZ=new T(function(){return B(unCStr("EOT"));}),_B0=4,_B1=function(_B2){var _B3=new T(function(){return B(A(_B2,[_B0]));}),_B4=function(_B5){return E(_B3);};return [1,B(_Aa(_AZ,_B4))];},_B6=new T(function(){return B(unCStr("ENQ"));}),_B7=5,_B8=function(_B9){var _Ba=new T(function(){return B(A(_B9,[_B7]));}),_Bb=function(_Bc){return E(_Ba);};return [1,B(_Aa(_B6,_Bb))];},_Bd=new T(function(){return B(unCStr("ACK"));}),_Be=6,_Bf=function(_Bg){var _Bh=new T(function(){return B(A(_Bg,[_Be]));}),_Bi=function(_Bj){return E(_Bh);};return [1,B(_Aa(_Bd,_Bi))];},_Bk=new T(function(){return B(unCStr("BEL"));}),_Bl=7,_Bm=function(_Bn){var _Bo=new T(function(){return B(A(_Bn,[_Bl]));}),_Bp=function(_Bq){return E(_Bo);};return [1,B(_Aa(_Bk,_Bp))];},_Br=new T(function(){return B(unCStr("BS"));}),_Bs=8,_Bt=function(_Bu){var _Bv=new T(function(){return B(A(_Bu,[_Bs]));}),_Bw=function(_Bx){return E(_Bv);};return [1,B(_Aa(_Br,_Bw))];},_By=new T(function(){return B(unCStr("HT"));}),_Bz=9,_BA=function(_BB){var _BC=new T(function(){return B(A(_BB,[_Bz]));}),_BD=function(_BE){return E(_BC);};return [1,B(_Aa(_By,_BD))];},_BF=new T(function(){return B(unCStr("LF"));}),_BG=10,_BH=function(_BI){var _BJ=new T(function(){return B(A(_BI,[_BG]));}),_BK=function(_BL){return E(_BJ);};return [1,B(_Aa(_BF,_BK))];},_BM=new T(function(){return B(unCStr("VT"));}),_BN=11,_BO=function(_BP){var _BQ=new T(function(){return B(A(_BP,[_BN]));}),_BR=function(_BS){return E(_BQ);};return [1,B(_Aa(_BM,_BR))];},_BT=new T(function(){return B(unCStr("FF"));}),_BU=12,_BV=function(_BW){var _BX=new T(function(){return B(A(_BW,[_BU]));}),_BY=function(_BZ){return E(_BX);};return [1,B(_Aa(_BT,_BY))];},_C0=new T(function(){return B(unCStr("CR"));}),_C1=13,_C2=function(_C3){var _C4=new T(function(){return B(A(_C3,[_C1]));}),_C5=function(_C6){return E(_C4);};return [1,B(_Aa(_C0,_C5))];},_C7=new T(function(){return B(unCStr("SI"));}),_C8=15,_C9=function(_Ca){var _Cb=new T(function(){return B(A(_Ca,[_C8]));}),_Cc=function(_Cd){return E(_Cb);};return [1,B(_Aa(_C7,_Cc))];},_Ce=new T(function(){return B(unCStr("DLE"));}),_Cf=16,_Cg=function(_Ch){var _Ci=new T(function(){return B(A(_Ch,[_Cf]));}),_Cj=function(_Ck){return E(_Ci);};return [1,B(_Aa(_Ce,_Cj))];},_Cl=new T(function(){return B(unCStr("DC1"));}),_Cm=17,_Cn=function(_Co){var _Cp=new T(function(){return B(A(_Co,[_Cm]));}),_Cq=function(_Cr){return E(_Cp);};return [1,B(_Aa(_Cl,_Cq))];},_Cs=new T(function(){return B(unCStr("DC2"));}),_Ct=18,_Cu=function(_Cv){var _Cw=new T(function(){return B(A(_Cv,[_Ct]));}),_Cx=function(_Cy){return E(_Cw);};return [1,B(_Aa(_Cs,_Cx))];},_Cz=new T(function(){return B(unCStr("DC3"));}),_CA=19,_CB=function(_CC){var _CD=new T(function(){return B(A(_CC,[_CA]));}),_CE=function(_CF){return E(_CD);};return [1,B(_Aa(_Cz,_CE))];},_CG=new T(function(){return B(unCStr("DC4"));}),_CH=20,_CI=function(_CJ){var _CK=new T(function(){return B(A(_CJ,[_CH]));}),_CL=function(_CM){return E(_CK);};return [1,B(_Aa(_CG,_CL))];},_CN=new T(function(){return B(unCStr("NAK"));}),_CO=21,_CP=function(_CQ){var _CR=new T(function(){return B(A(_CQ,[_CO]));}),_CS=function(_CT){return E(_CR);};return [1,B(_Aa(_CN,_CS))];},_CU=new T(function(){return B(unCStr("SYN"));}),_CV=22,_CW=function(_CX){var _CY=new T(function(){return B(A(_CX,[_CV]));}),_CZ=function(_D0){return E(_CY);};return [1,B(_Aa(_CU,_CZ))];},_D1=new T(function(){return B(unCStr("ETB"));}),_D2=23,_D3=function(_D4){var _D5=new T(function(){return B(A(_D4,[_D2]));}),_D6=function(_D7){return E(_D5);};return [1,B(_Aa(_D1,_D6))];},_D8=new T(function(){return B(unCStr("CAN"));}),_D9=24,_Da=function(_Db){var _Dc=new T(function(){return B(A(_Db,[_D9]));}),_Dd=function(_De){return E(_Dc);};return [1,B(_Aa(_D8,_Dd))];},_Df=new T(function(){return B(unCStr("EM"));}),_Dg=25,_Dh=function(_Di){var _Dj=new T(function(){return B(A(_Di,[_Dg]));}),_Dk=function(_Dl){return E(_Dj);};return [1,B(_Aa(_Df,_Dk))];},_Dm=new T(function(){return B(unCStr("SUB"));}),_Dn=26,_Do=function(_Dp){var _Dq=new T(function(){return B(A(_Dp,[_Dn]));}),_Dr=function(_Ds){return E(_Dq);};return [1,B(_Aa(_Dm,_Dr))];},_Dt=new T(function(){return B(unCStr("ESC"));}),_Du=27,_Dv=function(_Dw){var _Dx=new T(function(){return B(A(_Dw,[_Du]));}),_Dy=function(_Dz){return E(_Dx);};return [1,B(_Aa(_Dt,_Dy))];},_DA=new T(function(){return B(unCStr("FS"));}),_DB=28,_DC=function(_DD){var _DE=new T(function(){return B(A(_DD,[_DB]));}),_DF=function(_DG){return E(_DE);};return [1,B(_Aa(_DA,_DF))];},_DH=new T(function(){return B(unCStr("GS"));}),_DI=29,_DJ=function(_DK){var _DL=new T(function(){return B(A(_DK,[_DI]));}),_DM=function(_DN){return E(_DL);};return [1,B(_Aa(_DH,_DM))];},_DO=new T(function(){return B(unCStr("RS"));}),_DP=30,_DQ=function(_DR){var _DS=new T(function(){return B(A(_DR,[_DP]));}),_DT=function(_DU){return E(_DS);};return [1,B(_Aa(_DO,_DT))];},_DV=new T(function(){return B(unCStr("US"));}),_DW=31,_DX=function(_DY){var _DZ=new T(function(){return B(A(_DY,[_DW]));}),_E0=function(_E1){return E(_DZ);};return [1,B(_Aa(_DV,_E0))];},_E2=new T(function(){return B(unCStr("SP"));}),_E3=32,_E4=function(_E5){var _E6=new T(function(){return B(A(_E5,[_E3]));}),_E7=function(_E8){return E(_E6);};return [1,B(_Aa(_E2,_E7))];},_E9=new T(function(){return B(unCStr("DEL"));}),_Ea=127,_Eb=function(_Ec){var _Ed=new T(function(){return B(A(_Ec,[_Ea]));}),_Ee=function(_Ef){return E(_Ed);};return [1,B(_Aa(_E9,_Ee))];},_Eg=[1,_Eb,_3y],_Eh=[1,_E4,_Eg],_Ei=[1,_DX,_Eh],_Ej=[1,_DQ,_Ei],_Ek=[1,_DJ,_Ej],_El=[1,_DC,_Ek],_Em=[1,_Dv,_El],_En=[1,_Do,_Em],_Eo=[1,_Dh,_En],_Ep=[1,_Da,_Eo],_Eq=[1,_D3,_Ep],_Er=[1,_CW,_Eq],_Es=[1,_CP,_Er],_Et=[1,_CI,_Es],_Eu=[1,_CB,_Et],_Ev=[1,_Cu,_Eu],_Ew=[1,_Cn,_Ev],_Ex=[1,_Cg,_Ew],_Ey=[1,_C9,_Ex],_Ez=[1,_C2,_Ey],_EA=[1,_BV,_Ez],_EB=[1,_BO,_EA],_EC=[1,_BH,_EB],_ED=[1,_BA,_EC],_EE=[1,_Bt,_ED],_EF=[1,_Bm,_EE],_EG=[1,_Bf,_EF],_EH=[1,_B8,_EG],_EI=[1,_B1,_EH],_EJ=[1,_AU,_EI],_EK=[1,_AN,_EJ],_EL=[1,_AG,_EK],_EM=[1,_AC,_EL],_EN=new T(function(){return B(_A1(_EM));}),_EO=34,_EP=[0,1114111],_EQ=92,_ER=39,_ES=function(_ET){var _EU=new T(function(){return B(A(_ET,[_Bl]));}),_EV=new T(function(){return B(A(_ET,[_Bs]));}),_EW=new T(function(){return B(A(_ET,[_Bz]));}),_EX=new T(function(){return B(A(_ET,[_BG]));}),_EY=new T(function(){return B(A(_ET,[_BN]));}),_EZ=new T(function(){return B(A(_ET,[_BU]));}),_F0=new T(function(){return B(A(_ET,[_C1]));}),_F1=new T(function(){return B(A(_ET,[_EQ]));}),_F2=new T(function(){return B(A(_ET,[_ER]));}),_F3=new T(function(){return B(A(_ET,[_EO]));}),_F4=new T(function(){var _F5=function(_F6){var _F7=new T(function(){return B(_cW(E(_F6)));}),_F8=function(_F9){var _Fa=B(_yR(_F7,_F9));if(!B(_zR(_Fa,_EP))){return [2];}else{var _Fb=new T(function(){var _Fc=B(_zO(_Fa));if(_Fc>>>0>1114111){return B(_zL(_Fc));}else{return _Fc;}});return new F(function(){return A(_ET,[_Fb]);});}};return [1,B(_wD(_F6,_F8))];},_Fd=new T(function(){var _Fe=new T(function(){return B(A(_ET,[_DW]));}),_Ff=new T(function(){return B(A(_ET,[_DP]));}),_Fg=new T(function(){return B(A(_ET,[_DI]));}),_Fh=new T(function(){return B(A(_ET,[_DB]));}),_Fi=new T(function(){return B(A(_ET,[_Du]));}),_Fj=new T(function(){return B(A(_ET,[_Dn]));}),_Fk=new T(function(){return B(A(_ET,[_Dg]));}),_Fl=new T(function(){return B(A(_ET,[_D9]));}),_Fm=new T(function(){return B(A(_ET,[_D2]));}),_Fn=new T(function(){return B(A(_ET,[_CV]));}),_Fo=new T(function(){return B(A(_ET,[_CO]));}),_Fp=new T(function(){return B(A(_ET,[_CH]));}),_Fq=new T(function(){return B(A(_ET,[_CA]));}),_Fr=new T(function(){return B(A(_ET,[_Ct]));}),_Fs=new T(function(){return B(A(_ET,[_Cm]));}),_Ft=new T(function(){return B(A(_ET,[_Cf]));}),_Fu=new T(function(){return B(A(_ET,[_C8]));}),_Fv=new T(function(){return B(A(_ET,[_Ap]));}),_Fw=new T(function(){return B(A(_ET,[_Be]));}),_Fx=new T(function(){return B(A(_ET,[_B7]));}),_Fy=new T(function(){return B(A(_ET,[_B0]));}),_Fz=new T(function(){return B(A(_ET,[_AT]));}),_FA=new T(function(){return B(A(_ET,[_AM]));}),_FB=new T(function(){return B(A(_ET,[_Aw]));}),_FC=new T(function(){return B(A(_ET,[_AF]));}),_FD=function(_FE){switch(E(_FE)){case 64:return E(_FC);case 65:return E(_FB);case 66:return E(_FA);case 67:return E(_Fz);case 68:return E(_Fy);case 69:return E(_Fx);case 70:return E(_Fw);case 71:return E(_EU);case 72:return E(_EV);case 73:return E(_EW);case 74:return E(_EX);case 75:return E(_EY);case 76:return E(_EZ);case 77:return E(_F0);case 78:return E(_Fv);case 79:return E(_Fu);case 80:return E(_Ft);case 81:return E(_Fs);case 82:return E(_Fr);case 83:return E(_Fq);case 84:return E(_Fp);case 85:return E(_Fo);case 86:return E(_Fn);case 87:return E(_Fm);case 88:return E(_Fl);case 89:return E(_Fk);case 90:return E(_Fj);case 91:return E(_Fi);case 92:return E(_Fh);case 93:return E(_Fg);case 94:return E(_Ff);case 95:return E(_Fe);default:return [2];}},_FF=[0,_FD],_FG=new T(function(){return B(A(_EN,[_ET]));}),_FH=function(_FI){return (E(_FI)==94)?E(_FF):[2];};return B(_ux([0,_FH],_FG));});return B(_ux([1,B(_vT(_zH,_zJ,_F5))],_Fd));}),_FJ=function(_FK){switch(E(_FK)){case 34:return E(_F3);case 39:return E(_F2);case 92:return E(_F1);case 97:return E(_EU);case 98:return E(_EV);case 102:return E(_EZ);case 110:return E(_EX);case 114:return E(_F0);case 116:return E(_EW);case 118:return E(_EY);default:return [2];}};return new F(function(){return _ux([0,_FJ],_F4);});},_FL=function(_FM){return new F(function(){return A(_FM,[_9]);});},_FN=function(_FO){var _FP=E(_FO);if(!_FP[0]){return E(_FL);}else{var _FQ=_FP[2],_FR=E(_FP[1]),_FS=_FR>>>0,_FT=new T(function(){return B(_FN(_FQ));});if(_FS>887){var _FU=u_iswspace(_FR);if(!E(_FU)){return E(_FL);}else{var _FV=function(_FW){var _FX=new T(function(){return B(A(_FT,[_FW]));});return [0,function(_FY){return E(_FX);}];};return E(_FV);}}else{var _FZ=E(_FS);if(_FZ==32){var _G0=function(_G1){var _G2=new T(function(){return B(A(_FT,[_G1]));});return [0,function(_G3){return E(_G2);}];};return E(_G0);}else{if(_FZ-9>>>0>4){if(E(_FZ)==160){var _G4=function(_G5){var _G6=new T(function(){return B(A(_FT,[_G5]));});return [0,function(_G7){return E(_G6);}];};return E(_G4);}else{return E(_FL);}}else{var _G8=function(_G9){var _Ga=new T(function(){return B(A(_FT,[_G9]));});return [0,function(_Gb){return E(_Ga);}];};return E(_G8);}}}}},_Gc=function(_Gd){var _Ge=new T(function(){return B(_Gc(_Gd));}),_Gf=function(_Gg){return (E(_Gg)==92)?E(_Ge):[2];},_Gh=[0,_Gf],_Gi=function(_Gj){return E(_Gh);},_Gk=function(_Gl){return new F(function(){return A(_FN,[_Gl,_Gi]);});},_Gm=[1,_Gk],_Gn=new T(function(){var _Go=function(_Gp){return new F(function(){return A(_Gd,[[0,_Gp,_zB]]);});};return B(_ES(_Go));}),_Gq=function(_Gr){var _Gs=E(_Gr);if(_Gs==38){return E(_Ge);}else{var _Gt=_Gs>>>0;if(_Gt>887){var _Gu=u_iswspace(_Gs);return (E(_Gu)==0)?[2]:E(_Gm);}else{var _Gv=E(_Gt);return (_Gv==32)?E(_Gm):(_Gv-9>>>0>4)?(E(_Gv)==160)?E(_Gm):[2]:E(_Gm);}}},_Gw=[0,_Gq],_Gx=function(_Gy){var _Gz=E(_Gy);if(E(_Gz)==92){return E(_Gn);}else{return new F(function(){return A(_Gd,[[0,_Gz,_zA]]);});}},_GA=function(_GB){return (E(_GB)==92)?E(_Gw):[2];};return new F(function(){return _ux([0,_GA],[0,_Gx]);});},_GC=function(_GD,_GE){var _GF=new T(function(){var _GG=new T(function(){return B(A(_GD,[_3y]));});return B(A(_GE,[[1,_GG]]));}),_GH=function(_GI){var _GJ=E(_GI),_GK=E(_GJ[1]);if(E(_GK)==34){if(!E(_GJ[2])){return E(_GF);}else{var _GL=function(_GM){return new F(function(){return A(_GD,[[1,_GK,_GM]]);});};return new F(function(){return _GC(_GL,_GE);});}}else{var _GN=function(_GO){return new F(function(){return A(_GD,[[1,_GK,_GO]]);});};return new F(function(){return _GC(_GN,_GE);});}};return new F(function(){return _Gc(_GH);});},_GP=new T(function(){return B(unCStr("_\'"));}),_GQ=function(_GR){var _GS=u_iswalnum(_GR);if(!E(_GS)){return new F(function(){return _gz(_gy,_GR,_GP);});}else{return true;}},_GT=function(_GU){return new F(function(){return _GQ(E(_GU));});},_GV=new T(function(){return B(unCStr(",;()[]{}`"));}),_GW=new T(function(){return B(unCStr("=>"));}),_GX=[1,_GW,_3y],_GY=new T(function(){return B(unCStr("~"));}),_GZ=[1,_GY,_GX],_H0=new T(function(){return B(unCStr("@"));}),_H1=[1,_H0,_GZ],_H2=new T(function(){return B(unCStr("->"));}),_H3=[1,_H2,_H1],_H4=new T(function(){return B(unCStr("<-"));}),_H5=[1,_H4,_H3],_H6=new T(function(){return B(unCStr("|"));}),_H7=[1,_H6,_H5],_H8=new T(function(){return B(unCStr("\\"));}),_H9=[1,_H8,_H7],_Ha=new T(function(){return B(unCStr("="));}),_Hb=[1,_Ha,_H9],_Hc=new T(function(){return B(unCStr("::"));}),_Hd=[1,_Hc,_Hb],_He=new T(function(){return B(unCStr(".."));}),_Hf=[1,_He,_Hd],_Hg=function(_Hh){var _Hi=new T(function(){return B(A(_Hh,[_wA]));}),_Hj=new T(function(){var _Hk=new T(function(){var _Hl=function(_Hm){var _Hn=new T(function(){return B(A(_Hh,[[0,_Hm]]));});return [0,function(_Ho){return (E(_Ho)==39)?E(_Hn):[2];}];};return B(_ES(_Hl));}),_Hp=function(_Hq){var _Hr=E(_Hq);switch(E(_Hr)){case 39:return [2];case 92:return E(_Hk);default:var _Hs=new T(function(){return B(A(_Hh,[[0,_Hr]]));});return [0,function(_Ht){return (E(_Ht)==39)?E(_Hs):[2];}];}},_Hu=[0,_Hp],_Hv=new T(function(){var _Hw=new T(function(){return B(_GC(_S,_Hh));}),_Hx=new T(function(){var _Hy=new T(function(){var _Hz=new T(function(){var _HA=new T(function(){return [1,B(_vT(_xO,_zv,_Hh))];}),_HB=function(_HC){var _HD=E(_HC),_HE=u_iswalpha(_HD);if(!E(_HE)){if(E(_HD)==95){var _HF=function(_HG){return new F(function(){return A(_Hh,[[3,[1,_HD,_HG]]]);});};return [1,B(_wk(_GT,_HF))];}else{return [2];}}else{var _HH=function(_HI){return new F(function(){return A(_Hh,[[3,[1,_HD,_HI]]]);});};return [1,B(_wk(_GT,_HH))];}};return B(_ux([0,_HB],_HA));}),_HJ=function(_HK){if(!B(_gz(_gy,_HK,_zx))){return [2];}else{var _HL=function(_HM){var _HN=[1,_HK,_HM];if(!B(_gz(_vs,_HN,_Hf))){return new F(function(){return A(_Hh,[[4,_HN]]);});}else{return new F(function(){return A(_Hh,[[2,_HN]]);});}};return [1,B(_wk(_zy,_HL))];}};return B(_ux([0,_HJ],_Hz));}),_HO=function(_HP){if(!B(_gz(_gy,_HP,_GV))){return [2];}else{return new F(function(){return A(_Hh,[[2,[1,_HP,_3y]]]);});}};return B(_ux([0,_HO],_Hy));}),_HQ=function(_HR){return (E(_HR)==34)?E(_Hw):[2];};return B(_ux([0,_HQ],_Hx));}),_HS=function(_HT){return (E(_HT)==39)?E(_Hu):[2];};return B(_ux([0,_HS],_Hv));}),_HU=function(_HV){return (E(_HV)[0]==0)?E(_Hi):[2];};return new F(function(){return _ux([1,_HU],_Hj);});},_HW=0,_HX=function(_HY,_HZ){var _I0=new T(function(){var _I1=new T(function(){var _I2=function(_I3){var _I4=new T(function(){var _I5=new T(function(){return B(A(_HZ,[_I3]));}),_I6=function(_I7){var _I8=E(_I7);return (_I8[0]==2)?(!B(_2f(_I8[1],_vj)))?[2]:E(_I5):[2];};return B(_Hg(_I6));}),_I9=function(_Ia){return E(_I4);};return [1,function(_Ib){return new F(function(){return A(_FN,[_Ib,_I9]);});}];};return B(A(_HY,[_HW,_I2]));}),_Ic=function(_Id){var _Ie=E(_Id);return (_Ie[0]==2)?(!B(_2f(_Ie[1],_vi)))?[2]:E(_I1):[2];};return B(_Hg(_Ic));}),_If=function(_Ig){return E(_I0);};return function(_Ih){return new F(function(){return A(_FN,[_Ih,_If]);});};},_Ii=function(_Ij,_Ik){var _Il=function(_Im){var _In=new T(function(){return B(A(_Ij,[_Im]));}),_Io=function(_Ip){var _Iq=new T(function(){return [1,B(_HX(_Il,_Ip))];});return new F(function(){return _ux(B(A(_In,[_Ip])),_Iq);});};return E(_Io);},_Ir=new T(function(){return B(A(_Ij,[_Ik]));}),_Is=function(_It){var _Iu=new T(function(){return [1,B(_HX(_Il,_It))];});return new F(function(){return _ux(B(A(_Ir,[_It])),_Iu);});};return E(_Is);},_Iv=function(_Iw,_Ix){return new F(function(){return A(_Ix,[_2T]);});},_Iy=[0,_2Y,_Iv],_Iz=[1,_Iy,_3y],_IA=function(_IB,_IC){return new F(function(){return A(_IC,[_2V]);});},_ID=[0,_2X,_IA],_IE=[1,_ID,_Iz],_IF=function(_IG,_IH,_II){var _IJ=E(_IG);if(!_IJ[0]){return [2];}else{var _IK=_IJ[2],_IL=E(_IJ[1]),_IM=_IL[1],_IN=_IL[2],_IO=new T(function(){return B(A(_IN,[_IH,_II]));}),_IP=function(_IQ){var _IR=E(_IQ);switch(_IR[0]){case 3:return (!B(_2f(_IM,_IR[1])))?[2]:E(_IO);case 4:return (!B(_2f(_IM,_IR[1])))?[2]:E(_IO);default:return [2];}},_IS=new T(function(){return B(_Hg(_IP));}),_IT=function(_IU){return E(_IS);},_IV=new T(function(){return B(_IF(_IK,_IH,_II));}),_IW=function(_IX){return new F(function(){return A(_FN,[_IX,_IT]);});};return new F(function(){return _ux([1,_IW],_IV);});}},_IY=function(_IZ,_J0){return new F(function(){return _IF(_IE,_IZ,_J0);});},_J1=function(_J2){var _J3=[3,_J2,_vK],_J4=function(_J5){return E(_J3);};return [1,function(_J6){return new F(function(){return A(_FN,[_J6,_J4]);});}];},_J7=new T(function(){return B(A(_Ii,[_IY,_HW,_J1]));}),_J8=new T(function(){return B(err(_tc));}),_J9=new T(function(){return B(err(_te));}),_Ja=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:50:3-15"));}),_Jb=[0,_75,_76,_3y,_Ja,_75,_75],_Jc=new T(function(){return B(_73(_Jb));}),_Jd=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:51:3-15"));}),_Je=[0,_75,_76,_3y,_Jd,_75,_75],_Jf=new T(function(){return B(_73(_Je));}),_Jg=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:52:3-14"));}),_Jh=[0,_75,_76,_3y,_Jg,_75,_75],_Ji=new T(function(){return B(_73(_Jh));}),_Jj=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:53:3-11"));}),_Jk=[0,_75,_76,_3y,_Jj,_75,_75],_Jl=new T(function(){return B(_73(_Jk));}),_Jm=function(_Jn,_Jo){var _Jp=function(_Jq,_Jr){var _Js=function(_Jt){var _Ju=new T(function(){return  -E(_Jt);});return new F(function(){return A(_Jr,[_Ju]);});},_Jv=function(_Jw){return new F(function(){return A(_Jn,[_Jw,_Jq,_Js]);});},_Jx=new T(function(){return B(_Hg(_Jv));}),_Jy=function(_Jz){return E(_Jx);},_JA=function(_JB){return new F(function(){return A(_FN,[_JB,_Jy]);});},_JC=[1,_JA],_JD=function(_JE){var _JF=E(_JE);if(_JF[0]==4){var _JG=E(_JF[1]);if(!_JG[0]){return new F(function(){return A(_Jn,[_JF,_Jq,_Jr]);});}else{if(E(_JG[1])==45){if(!E(_JG[2])[0]){return E(_JC);}else{return new F(function(){return A(_Jn,[_JF,_Jq,_Jr]);});}}else{return new F(function(){return A(_Jn,[_JF,_Jq,_Jr]);});}}}else{return new F(function(){return A(_Jn,[_JF,_Jq,_Jr]);});}},_JH=new T(function(){return B(_Hg(_JD));}),_JI=function(_JJ){return E(_JH);};return [1,function(_JK){return new F(function(){return A(_FN,[_JK,_JI]);});}];};return new F(function(){return _Ii(_Jp,_Jo);});},_JL=new T(function(){return 1/0;}),_JM=function(_JN,_JO){return new F(function(){return A(_JO,[_JL]);});},_JP=new T(function(){return 0/0;}),_JQ=function(_JR,_JS){return new F(function(){return A(_JS,[_JP]);});},_JT=new T(function(){return B(unCStr("NaN"));}),_JU=new T(function(){return B(unCStr("Infinity"));}),_JV=1024,_JW=-1021,_JX=new T(function(){return B(unCStr("GHC.Exception"));}),_JY=new T(function(){return B(unCStr("base"));}),_JZ=new T(function(){return B(unCStr("ArithException"));}),_K0=new T(function(){var _K1=hs_wordToWord64(4194982440),_K2=hs_wordToWord64(3110813675);return [0,_K1,_K2,[0,_K1,_K2,_JY,_JX,_JZ],_3y,_3y];}),_K3=function(_K4){return E(_K0);},_K5=function(_K6){var _K7=E(_K6);return new F(function(){return _5p(B(_5n(_K7[1])),_K3,_K7[2]);});},_K8=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_K9=new T(function(){return B(unCStr("denormal"));}),_Ka=new T(function(){return B(unCStr("divide by zero"));}),_Kb=new T(function(){return B(unCStr("loss of precision"));}),_Kc=new T(function(){return B(unCStr("arithmetic underflow"));}),_Kd=new T(function(){return B(unCStr("arithmetic overflow"));}),_Ke=function(_Kf,_Kg){switch(E(_Kf)){case 0:return new F(function(){return _18(_Kd,_Kg);});break;case 1:return new F(function(){return _18(_Kc,_Kg);});break;case 2:return new F(function(){return _18(_Kb,_Kg);});break;case 3:return new F(function(){return _18(_Ka,_Kg);});break;case 4:return new F(function(){return _18(_K9,_Kg);});break;default:return new F(function(){return _18(_K8,_Kg);});}},_Kh=function(_Ki){return new F(function(){return _Ke(_Ki,_3y);});},_Kj=function(_Kk,_Kl,_Km){return new F(function(){return _Ke(_Kl,_Km);});},_Kn=function(_Ko,_Kp){return new F(function(){return _6H(_Ke,_Ko,_Kp);});},_Kq=[0,_Kj,_Kh,_Kn],_Kr=new T(function(){return [0,_K3,_Kq,_Ks,_K5,_Kh];}),_Ks=function(_tQ){return [0,_Kr,_tQ];},_Kt=3,_Ku=new T(function(){return B(_Ks(_Kt));}),_Kv=new T(function(){return die(_Ku);}),_Kw=function(_Kx,_Ky){var _Kz=E(_Kx);if(!_Kz[0]){var _KA=_Kz[1],_KB=E(_Ky);return (_KB[0]==0)?_KA==_KB[1]:(I_compareInt(_KB[1],_KA)==0)?true:false;}else{var _KC=_Kz[1],_KD=E(_Ky);return (_KD[0]==0)?(I_compareInt(_KC,_KD[1])==0)?true:false:(I_compare(_KC,_KD[1])==0)?true:false;}},_KE=[0,0],_KF=function(_KG,_KH){while(1){var _KI=E(_KG);if(!_KI[0]){var _KJ=E(_KI[1]);if(_KJ==(-2147483648)){_KG=[1,I_fromInt(-2147483648)];continue;}else{var _KK=E(_KH);if(!_KK[0]){return [0,_KJ%_KK[1]];}else{_KG=[1,I_fromInt(_KJ)];_KH=_KK;continue;}}}else{var _KL=_KI[1],_KM=E(_KH);return (_KM[0]==0)?[1,I_rem(_KL,I_fromInt(_KM[1]))]:[1,I_rem(_KL,_KM[1])];}}},_KN=function(_KO,_KP){if(!B(_Kw(_KP,_KE))){return new F(function(){return _KF(_KO,_KP);});}else{return E(_Kv);}},_KQ=function(_KR,_KS){while(1){if(!B(_Kw(_KS,_KE))){var _KT=_KS,_KU=B(_KN(_KR,_KS));_KR=_KT;_KS=_KU;continue;}else{return E(_KR);}}},_KV=function(_KW){var _KX=E(_KW);if(!_KX[0]){var _KY=E(_KX[1]);return (_KY==(-2147483648))?E(_y6):(_KY<0)?[0, -_KY]:E(_KX);}else{var _KZ=_KX[1];return (I_compareInt(_KZ,0)>=0)?E(_KX):[1,I_negate(_KZ)];}},_L0=function(_L1,_L2){while(1){var _L3=E(_L1);if(!_L3[0]){var _L4=E(_L3[1]);if(_L4==(-2147483648)){_L1=[1,I_fromInt(-2147483648)];continue;}else{var _L5=E(_L2);if(!_L5[0]){return [0,quot(_L4,_L5[1])];}else{_L1=[1,I_fromInt(_L4)];_L2=_L5;continue;}}}else{var _L6=_L3[1],_L7=E(_L2);return (_L7[0]==0)?[0,I_toInt(I_quot(_L6,I_fromInt(_L7[1])))]:[1,I_quot(_L6,_L7[1])];}}},_L8=5,_L9=new T(function(){return B(_Ks(_L8));}),_La=new T(function(){return die(_L9);}),_Lb=function(_Lc,_Ld){if(!B(_Kw(_Ld,_KE))){var _Le=B(_KQ(B(_KV(_Lc)),B(_KV(_Ld))));return (!B(_Kw(_Le,_KE)))?[0,B(_L0(_Lc,_Le)),B(_L0(_Ld,_Le))]:E(_Kv);}else{return E(_La);}},_Lf=[0,1],_Lg=new T(function(){return B(unCStr("Negative exponent"));}),_Lh=new T(function(){return B(err(_Lg));}),_Li=[0,2],_Lj=new T(function(){return B(_Kw(_Li,_KE));}),_Lk=function(_Ll,_Lm){while(1){var _Ln=E(_Ll);if(!_Ln[0]){var _Lo=_Ln[1],_Lp=E(_Lm);if(!_Lp[0]){var _Lq=_Lp[1],_Lr=subC(_Lo,_Lq);if(!E(_Lr[2])){return [0,_Lr[1]];}else{_Ll=[1,I_fromInt(_Lo)];_Lm=[1,I_fromInt(_Lq)];continue;}}else{_Ll=[1,I_fromInt(_Lo)];_Lm=_Lp;continue;}}else{var _Ls=E(_Lm);if(!_Ls[0]){_Ll=_Ln;_Lm=[1,I_fromInt(_Ls[1])];continue;}else{return [1,I_sub(_Ln[1],_Ls[1])];}}}},_Lt=function(_Lu,_Lv,_Lw){while(1){if(!E(_Lj)){if(!B(_Kw(B(_KF(_Lv,_Li)),_KE))){if(!B(_Kw(_Lv,_Lf))){var _Lx=B(_yl(_Lu,_Lu)),_Ly=B(_L0(B(_Lk(_Lv,_Lf)),_Li)),_Lz=B(_yl(_Lu,_Lw));_Lu=_Lx;_Lv=_Ly;_Lw=_Lz;continue;}else{return new F(function(){return _yl(_Lu,_Lw);});}}else{var _Lx=B(_yl(_Lu,_Lu)),_Ly=B(_L0(_Lv,_Li));_Lu=_Lx;_Lv=_Ly;continue;}}else{return E(_Kv);}}},_LA=function(_LB,_LC){while(1){if(!E(_Lj)){if(!B(_Kw(B(_KF(_LC,_Li)),_KE))){if(!B(_Kw(_LC,_Lf))){return new F(function(){return _Lt(B(_yl(_LB,_LB)),B(_L0(B(_Lk(_LC,_Lf)),_Li)),_LB);});}else{return E(_LB);}}else{var _LD=B(_yl(_LB,_LB)),_LE=B(_L0(_LC,_Li));_LB=_LD;_LC=_LE;continue;}}else{return E(_Kv);}}},_LF=function(_LG,_LH){if(!B(_lN(_LH,_KE))){if(!B(_Kw(_LH,_KE))){return new F(function(){return _LA(_LG,_LH);});}else{return E(_Lf);}}else{return E(_Lh);}},_LI=[0,1],_LJ=[0,0],_LK=[0,-1],_LL=function(_LM){var _LN=E(_LM);if(!_LN[0]){var _LO=_LN[1];return (_LO>=0)?(E(_LO)==0)?E(_LJ):E(_xV):E(_LK);}else{var _LP=I_compareInt(_LN[1],0);return (_LP<=0)?(E(_LP)==0)?E(_LJ):E(_LK):E(_xV);}},_LQ=function(_LR,_LS,_LT){while(1){var _LU=E(_LT);if(!_LU[0]){if(!B(_lN(_LR,_yA))){return [0,B(_yl(_LS,B(_LF(_yb,_LR)))),_Lf];}else{var _LV=B(_LF(_yb,B(_y7(_LR))));return new F(function(){return _Lb(B(_yl(_LS,B(_LL(_LV)))),B(_KV(_LV)));});}}else{var _LW=B(_Lk(_LR,_LI)),_LX=B(_xX(B(_yl(_LS,_yb)),B(_cW(E(_LU[1])))));_LT=_LU[2];_LR=_LW;_LS=_LX;continue;}}},_LY=function(_LZ,_M0){var _M1=E(_LZ);if(!_M1[0]){var _M2=_M1[1],_M3=E(_M0);return (_M3[0]==0)?_M2>=_M3[1]:I_compareInt(_M3[1],_M2)<=0;}else{var _M4=_M1[1],_M5=E(_M0);return (_M5[0]==0)?I_compareInt(_M4,_M5[1])>=0:I_compare(_M4,_M5[1])>=0;}},_M6=function(_M7){var _M8=E(_M7);if(!_M8[0]){var _M9=_M8[1],_Ma=_M8[2],_Mb=new T(function(){return B(_yc(_Ma,0));},1),_Mc=new T(function(){return B(_cW(E(_M9)));});return new F(function(){return _Lb(B(_yl(B(_yB(_Mc,_Mb,B(_1F(_yh,_Ma)))),_LI)),_LI);});}else{var _Md=_M8[1],_Me=_M8[3],_Mf=E(_M8[2]);if(!_Mf[0]){var _Mg=E(_Me);if(!_Mg[0]){return new F(function(){return _Lb(B(_yl(B(_yR(_yb,_Md)),_LI)),_LI);});}else{var _Mh=_Mg[1];if(!B(_LY(_Mh,_yA))){var _Mi=B(_LF(_yb,B(_y7(_Mh))));return new F(function(){return _Lb(B(_yl(B(_yR(_yb,_Md)),B(_LL(_Mi)))),B(_KV(_Mi)));});}else{return new F(function(){return _Lb(B(_yl(B(_yl(B(_yR(_yb,_Md)),B(_LF(_yb,_Mh)))),_LI)),_LI);});}}}else{var _Mj=_Mf[1],_Mk=E(_Me);if(!_Mk[0]){return new F(function(){return _LQ(_yA,B(_yR(_yb,_Md)),_Mj);});}else{return new F(function(){return _LQ(_Mk[1],B(_yR(_yb,_Md)),_Mj);});}}}},_Ml=function(_Mm,_Mn){while(1){var _Mo=E(_Mn);if(!_Mo[0]){return [0];}else{if(!B(A(_Mm,[_Mo[1]]))){return E(_Mo);}else{_Mn=_Mo[2];continue;}}}},_Mp=function(_Mq,_Mr){var _Ms=E(_Mq);if(!_Ms[0]){var _Mt=_Ms[1],_Mu=E(_Mr);return (_Mu[0]==0)?_Mt>_Mu[1]:I_compareInt(_Mu[1],_Mt)<0;}else{var _Mv=_Ms[1],_Mw=E(_Mr);return (_Mw[0]==0)?I_compareInt(_Mv,_Mw[1])>0:I_compare(_Mv,_Mw[1])>0;}},_Mx=0,_My=function(_Mz,_MA){return E(_Mz)==E(_MA);},_MB=function(_MC){return new F(function(){return _My(_Mx,_MC);});},_MD=[0,E(_yA),E(_Lf)],_ME=[1,_MD],_MF=[0,-2147483648],_MG=[0,2147483647],_MH=function(_MI,_MJ,_MK){var _ML=E(_MK);if(!_ML[0]){return [1,new T(function(){var _MM=B(_M6(_ML));return [0,E(_MM[1]),E(_MM[2])];})];}else{var _MN=E(_ML[3]);if(!_MN[0]){return [1,new T(function(){var _MO=B(_M6(_ML));return [0,E(_MO[1]),E(_MO[2])];})];}else{var _MP=_MN[1];if(!B(_Mp(_MP,_MG))){if(!B(_lN(_MP,_MF))){var _MQ=function(_MR){var _MS=_MR+B(_zO(_MP))|0;if(_MS<=(E(_MJ)+3|0)){if(_MS>=(E(_MI)-3|0)){return [1,new T(function(){var _MT=B(_M6(_ML));return [0,E(_MT[1]),E(_MT[2])];})];}else{return E(_ME);}}else{return [0];}},_MU=B(_Ml(_MB,_ML[1]));if(!_MU[0]){var _MV=E(_ML[2]);if(!_MV[0]){return E(_ME);}else{var _MW=B(_tR(_MB,_MV[1]));if(!E(_MW[2])[0]){return E(_ME);}else{return new F(function(){return _MQ( -B(_yc(_MW[1],0)));});}}}else{return new F(function(){return _MQ(B(_yc(_MU,0)));});}}else{return [0];}}else{return [0];}}}},_MX=function(_MY,_MZ){return [2];},_N0=[0,1],_N1=function(_N2,_N3){var _N4=E(_N2);if(!_N4[0]){var _N5=_N4[1],_N6=E(_N3);if(!_N6[0]){var _N7=_N6[1];return (_N5!=_N7)?(_N5>_N7)?2:0:1;}else{var _N8=I_compareInt(_N6[1],_N5);return (_N8<=0)?(_N8>=0)?1:2:0;}}else{var _N9=_N4[1],_Na=E(_N3);if(!_Na[0]){var _Nb=I_compareInt(_N9,_Na[1]);return (_Nb>=0)?(_Nb<=0)?1:2:0;}else{var _Nc=I_compare(_N9,_Na[1]);return (_Nc>=0)?(_Nc<=0)?1:2:0;}}},_Nd=function(_Ne,_Nf){var _Ng=E(_Ne);return (_Ng[0]==0)?_Ng[1]*Math.pow(2,_Nf):I_toNumber(_Ng[1])*Math.pow(2,_Nf);},_Nh=function(_Ni,_Nj){while(1){var _Nk=E(_Ni);if(!_Nk[0]){var _Nl=E(_Nk[1]);if(_Nl==(-2147483648)){_Ni=[1,I_fromInt(-2147483648)];continue;}else{var _Nm=E(_Nj);if(!_Nm[0]){var _Nn=_Nm[1];return [0,[0,quot(_Nl,_Nn)],[0,_Nl%_Nn]];}else{_Ni=[1,I_fromInt(_Nl)];_Nj=_Nm;continue;}}}else{var _No=E(_Nj);if(!_No[0]){_Ni=_Nk;_Nj=[1,I_fromInt(_No[1])];continue;}else{var _Np=I_quotRem(_Nk[1],_No[1]);return [0,[1,_Np[1]],[1,_Np[2]]];}}}},_Nq=[0,0],_Nr=function(_Ns,_Nt,_Nu){if(!B(_Kw(_Nu,_Nq))){var _Nv=B(_Nh(_Nt,_Nu)),_Nw=_Nv[1];switch(B(_N1(B(_e2(_Nv[2],1)),_Nu))){case 0:return new F(function(){return _Nd(_Nw,_Ns);});break;case 1:if(!(B(_zO(_Nw))&1)){return new F(function(){return _Nd(_Nw,_Ns);});}else{return new F(function(){return _Nd(B(_xX(_Nw,_N0)),_Ns);});}break;default:return new F(function(){return _Nd(B(_xX(_Nw,_N0)),_Ns);});}}else{return E(_Kv);}},_Nx=function(_Ny){var _Nz=_xV,_NA=0;while(1){if(!B(_lN(_Nz,_Ny))){if(!B(_Mp(_Nz,_Ny))){if(!B(_Kw(_Nz,_Ny))){return new F(function(){return _uh("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_NA);}}else{return _NA-1|0;}}else{var _NB=B(_e2(_Nz,1)),_NC=_NA+1|0;_Nz=_NB;_NA=_NC;continue;}}},_ND=function(_NE){var _NF=E(_NE);if(!_NF[0]){var _NG=_NF[1]>>>0;if(!_NG){return -1;}else{var _NH=1,_NI=0;while(1){if(_NH>=_NG){if(_NH<=_NG){if(_NH!=_NG){return new F(function(){return _uh("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_NI);}}else{return _NI-1|0;}}else{var _NJ=imul(_NH,2)>>>0,_NK=_NI+1|0;_NH=_NJ;_NI=_NK;continue;}}}}else{return new F(function(){return _Nx(_NF);});}},_NL=function(_NM){var _NN=E(_NM);if(!_NN[0]){var _NO=_NN[1]>>>0;if(!_NO){return [0,-1,0];}else{var _NP=function(_NQ,_NR){while(1){if(_NQ>=_NO){if(_NQ<=_NO){if(_NQ!=_NO){return new F(function(){return _uh("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_NR);}}else{return _NR-1|0;}}else{var _NS=imul(_NQ,2)>>>0,_NT=_NR+1|0;_NQ=_NS;_NR=_NT;continue;}}};return [0,B(_NP(1,0)),(_NO&_NO-1>>>0)>>>0&4294967295];}}else{var _NU=B(_ND(_NN)),_NV=_NU>>>0;if(!_NV){var _NW=E(_NU);return (_NW==(-2))?[0,-2,0]:[0,_NW,1];}else{var _NX=function(_NY,_NZ){while(1){if(_NY>=_NV){if(_NY<=_NV){if(_NY!=_NV){return new F(function(){return _uh("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_NZ);}}else{return _NZ-1|0;}}else{var _O0=imul(_NY,2)>>>0,_O1=_NZ+1|0;_NY=_O0;_NZ=_O1;continue;}}},_O2=B(_NX(1,0));return ((_O2+_O2|0)!=_NU)?[0,_NU,1]:[0,_NU,0];}}},_O3=function(_O4,_O5){while(1){var _O6=E(_O4);if(!_O6[0]){var _O7=_O6[1],_O8=E(_O5);if(!_O8[0]){return [0,(_O7>>>0&_O8[1]>>>0)>>>0&4294967295];}else{_O4=[1,I_fromInt(_O7)];_O5=_O8;continue;}}else{var _O9=E(_O5);if(!_O9[0]){_O4=_O6;_O5=[1,I_fromInt(_O9[1])];continue;}else{return [1,I_and(_O6[1],_O9[1])];}}}},_Oa=[0,2],_Ob=function(_Oc,_Od){var _Oe=E(_Oc);if(!_Oe[0]){var _Of=(_Oe[1]>>>0&(2<<_Od>>>0)-1>>>0)>>>0,_Og=1<<_Od>>>0;return (_Og<=_Of)?(_Og>=_Of)?1:2:0;}else{var _Oh=B(_O3(_Oe,B(_Lk(B(_e2(_Oa,_Od)),_xV)))),_Oi=B(_e2(_xV,_Od));return (!B(_Mp(_Oi,_Oh)))?(!B(_lN(_Oi,_Oh)))?1:2:0;}},_Oj=function(_Ok,_Ol){while(1){var _Om=E(_Ok);if(!_Om[0]){_Ok=[1,I_fromInt(_Om[1])];continue;}else{return [1,I_shiftRight(_Om[1],_Ol)];}}},_On=function(_Oo,_Op,_Oq,_Or){var _Os=B(_NL(_Or)),_Ot=_Os[1];if(!E(_Os[2])){var _Ou=B(_ND(_Oq));if(_Ou<((_Ot+_Oo|0)-1|0)){var _Ov=_Ot+(_Oo-_Op|0)|0;if(_Ov>0){if(_Ov>_Ou){if(_Ov<=(_Ou+1|0)){if(!E(B(_NL(_Oq))[2])){return 0;}else{return new F(function(){return _Nd(_N0,_Oo-_Op|0);});}}else{return 0;}}else{var _Ow=B(_Oj(_Oq,_Ov));switch(B(_Ob(_Oq,_Ov-1|0))){case 0:return new F(function(){return _Nd(_Ow,_Oo-_Op|0);});break;case 1:if(!(B(_zO(_Ow))&1)){return new F(function(){return _Nd(_Ow,_Oo-_Op|0);});}else{return new F(function(){return _Nd(B(_xX(_Ow,_N0)),_Oo-_Op|0);});}break;default:return new F(function(){return _Nd(B(_xX(_Ow,_N0)),_Oo-_Op|0);});}}}else{return new F(function(){return _Nd(_Oq,(_Oo-_Op|0)-_Ov|0);});}}else{if(_Ou>=_Op){var _Ox=B(_Oj(_Oq,(_Ou+1|0)-_Op|0));switch(B(_Ob(_Oq,_Ou-_Op|0))){case 0:return new F(function(){return _Nd(_Ox,((_Ou-_Ot|0)+1|0)-_Op|0);});break;case 2:return new F(function(){return _Nd(B(_xX(_Ox,_N0)),((_Ou-_Ot|0)+1|0)-_Op|0);});break;default:if(!(B(_zO(_Ox))&1)){return new F(function(){return _Nd(_Ox,((_Ou-_Ot|0)+1|0)-_Op|0);});}else{return new F(function(){return _Nd(B(_xX(_Ox,_N0)),((_Ou-_Ot|0)+1|0)-_Op|0);});}}}else{return new F(function(){return _Nd(_Oq, -_Ot);});}}}else{var _Oy=B(_ND(_Oq))-_Ot|0,_Oz=function(_OA){var _OB=function(_OC,_OD){if(!B(_zR(B(_e2(_OD,_Op)),_OC))){return new F(function(){return _Nr(_OA-_Op|0,_OC,_OD);});}else{return new F(function(){return _Nr((_OA-_Op|0)+1|0,_OC,B(_e2(_OD,1)));});}};if(_OA>=_Op){if(_OA!=_Op){var _OE=new T(function(){return B(_e2(_Or,_OA-_Op|0));});return new F(function(){return _OB(_Oq,_OE);});}else{return new F(function(){return _OB(_Oq,_Or);});}}else{var _OF=new T(function(){return B(_e2(_Oq,_Op-_OA|0));});return new F(function(){return _OB(_OF,_Or);});}};if(_Oo>_Oy){return new F(function(){return _Oz(_Oo);});}else{return new F(function(){return _Oz(_Oy);});}}},_OG=new T(function(){return 0/0;}),_OH=new T(function(){return -1/0;}),_OI=new T(function(){return 1/0;}),_OJ=0,_OK=function(_OL,_OM){if(!B(_Kw(_OM,_Nq))){if(!B(_Kw(_OL,_Nq))){if(!B(_lN(_OL,_Nq))){return new F(function(){return _On(-1021,53,_OL,_OM);});}else{return  -B(_On(-1021,53,B(_y7(_OL)),_OM));}}else{return E(_OJ);}}else{return (!B(_Kw(_OL,_Nq)))?(!B(_lN(_OL,_Nq)))?E(_OI):E(_OH):E(_OG);}},_ON=function(_OO){var _OP=E(_OO);switch(_OP[0]){case 3:var _OQ=_OP[1];return (!B(_2f(_OQ,_JU)))?(!B(_2f(_OQ,_JT)))?E(_MX):E(_JQ):E(_JM);case 5:var _OR=B(_MH(_JW,_JV,_OP[1]));if(!_OR[0]){return E(_JM);}else{var _OS=_OR[1],_OT=new T(function(){var _OU=E(_OS);return B(_OK(_OU[1],_OU[2]));}),_OV=function(_OW,_OX){return new F(function(){return A(_OX,[_OT]);});};return E(_OV);}break;default:return E(_MX);}},_OY=new T(function(){return B(A(_Jm,[_ON,_HW,_J1]));}),_OZ=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:62:3-10"));}),_P0=[0,_75,_76,_3y,_OZ,_75,_75],_P1=new T(function(){return B(_73(_P0));}),_P2=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:63:3-11"));}),_P3=[0,_75,_76,_3y,_P2,_75,_75],_P4=new T(function(){return B(_73(_P3));}),_P5=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:72:3-12"));}),_P6=[0,_75,_76,_3y,_P5,_75,_75],_P7=new T(function(){return B(_73(_P6));}),_P8=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:73:3-12"));}),_P9=[0,_75,_76,_3y,_P8,_75,_75],_Pa=new T(function(){return B(_73(_P9));}),_Pb=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:74:3-11"));}),_Pc=[0,_75,_76,_3y,_Pb,_75,_75],_Pd=new T(function(){return B(_73(_Pc));}),_Pe=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:89:3-14"));}),_Pf=[0,_75,_76,_3y,_Pe,_75,_75],_Pg=new T(function(){return B(_73(_Pf));}),_Ph=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:90:3-11"));}),_Pi=[0,_75,_76,_3y,_Ph,_75,_75],_Pj=new T(function(){return B(_73(_Pi));}),_Pk=function(_Pl){while(1){var _Pm=(function(_Pn){var _Po=E(_Pn);if(!_Po[0]){return [0];}else{var _Pp=_Po[2],_Pq=E(_Po[1]);if(!E(_Pq[2])[0]){var _Pr=new T(function(){return B(_Pk(_Pp));});return [1,_Pq[1],_Pr];}else{_Pl=_Pp;return null;}}})(_Pl);if(_Pm!=null){return _Pm;}}},_Ps=function(_Pt,_Pu){var _Pv=new T(function(){var _Pw=B(_Pk(B(_ul(_OY,_Pt))));if(!_Pw[0]){return E(_J8);}else{if(!E(_Pw[2])[0]){return E(_Pw[1])*1.7453292519943295e-2;}else{return E(_J9);}}});return [1,_Pv,_Pu];},_Px=function(_){return _9;},_Py=new T(function(){return B(unCStr("loadPath"));}),_Pz=function(_PA,_){var _PB=function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);},_PC=_PB,_PD=new T(function(){return E(_PC);}),_PE=E(_PD)("processDump",toJSStr(_Py));return new F(function(){return _Px(_);});},_PF=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:121:5-17"));}),_PG=[0,_75,_76,_3y,_PF,_75,_75],_PH=new T(function(){return B(_73(_PG));}),_PI=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:124:5-19"));}),_PJ=[0,_75,_76,_3y,_PI,_75,_75],_PK=new T(function(){return B(_73(_PJ));}),_PL=new T(function(){return B(unCStr("download"));}),_PM=new T(function(){return B(unCStr(".txt"));}),_PN=new T(function(){return B(unCStr(".json"));}),_PO=new T(function(){return B(unCStr("filePath"));}),_PP=new T(function(){return B(unCStr("IndianRoller2.jpg"));}),_PQ=function(_PR,_PS){var _PT=E(_PS);if(!_PT[0]){return [0,_3y,_3y];}else{var _PU=_PT[1],_PV=_PT[2];if(!B(A(_PR,[_PU]))){var _PW=new T(function(){var _PX=B(_PQ(_PR,_PV));return [0,_PX[1],_PX[2]];}),_PY=new T(function(){return E(E(_PW)[2]);}),_PZ=new T(function(){return E(E(_PW)[1]);});return [0,[1,_PU,_PZ],_PY];}else{return [0,_3y,_PT];}}},_Q0=function(_Q1){var _Q2=_Q1>>>0;if(_Q2>887){var _Q3=u_iswspace(_Q1);return (E(_Q3)==0)?false:true;}else{var _Q4=E(_Q2);return (_Q4==32)?true:(_Q4-9>>>0>4)?(E(_Q4)==160)?true:false:true;}},_Q5=function(_Q6){return new F(function(){return _Q0(E(_Q6));});},_Q7=function(_Q8,_Q9,_Qa){var _Qb=function(_Qc){var _Qd=B(_Ml(_Q5,_Qc));if(!_Qd[0]){return E(_Q9);}else{var _Qe=new T(function(){var _Qf=B(_PQ(_Q5,_Qd));return [0,_Qf[1],_Qf[2]];}),_Qg=new T(function(){return B(_Qb(E(_Qe)[2]));}),_Qh=new T(function(){return E(E(_Qe)[1]);});return new F(function(){return A(_Q8,[_Qh,_Qg]);});}};return new F(function(){return _Qb(_Qa);});},_Qi=function(_){var _Qj=jsFind("filePath");if(!_Qj[0]){return new F(function(){return die(_Jc);});}else{var _Qk=jsFind("loadPath");if(!_Qk[0]){return new F(function(){return die(_Jf);});}else{var _Ql="runfile",_Qm=jsFind(_Ql);if(!_Qm[0]){return new F(function(){return die(_Ji);});}else{var _Qn=_Qm[1],_Qo="rotations",_Qp=jsFind(_Qo);if(!_Qp[0]){return new F(function(){return die(_Jl);});}else{var _Qq=_Qp[1],_Qr=nMV(_t3),_Qs=_Qr,_Qt=nMV(_tb),_Qu=_Qt,_Qv=B(A(_3,[_7e,_PP,_])),_Qw=nMV(_Qv),_Qx=_Qw,_Qy=nMV(_PP),_Qz=_Qy,_QA=B(A(_kS,[_7e,_kZ,_])),_QB=E(_QA);if(!_QB[0]){return new F(function(){return die(_P1);});}else{var _QC=B(A(_kS,[_7e,_kX,_])),_QD=E(_QC);if(!_QD[0]){return new F(function(){return die(_P4);});}else{var _QE=_Qu,_QF=_Qx,_QG=function(_){return new F(function(){return _p4(_QE,_Qs,_QF,_);});},_QH=B(_qR(_Qs,_QB[1],_QG,_)),_QI=B(_sm(_QE,_QD[1],_QG,_)),_QJ=function(_QK,_){var _QL=String(E(_QK)),_QM=jsParseJSON(_QL);if(!_QM[0]){return _9V;}else{var _QN=B(_4A(_QM[1]));if(!_QN[0]){return _9V;}else{var _QO=_QN[1],_QP=new T(function(){return E(E(_QO)[1]);}),_=wMV(_Qs,_QP),_QQ=new T(function(){return E(E(_QO)[2]);}),_=wMV(_Qu,_QQ);return _9V;}}},_QR=__createJSFunc(2,E(_QJ)),_QS=(function(s,f){Haste[s] = f;}),_QT=_QS,_QU=new T(function(){return E(_QT);}),_QV=E(_QU)("processDump",_QR),_QW="top",_QX=jsFind(_QW);if(!_QX[0]){return new F(function(){return die(_P7);});}else{var _QY=_QX[1],_QZ="bottom",_R0=jsFind(_QZ);if(!_R0[0]){return new F(function(){return die(_Pa);});}else{var _R1=_R0[1],_R2="offset",_R3=jsFind(_R2);if(!_R3[0]){return new F(function(){return die(_Pd);});}else{var _R4=_R3[1],_R5=E(_sQ),_R6=jsQuerySelectorAll(_R5,"input[name=\'mount\']"),_R7=function(_R8,_){var _R9=E(_R8),_Ra=toJSStr(_PO),_Rb=E(_sR)(_Ra),_Rc=_Rb,_Rd=new T(function(){var _Re=String(_Rc);return fromJSStr(_Re);}),_Rf=B(A(_3,[_7e,_Rd,_])),_=wMV(_Qx,_Rf),_Rg=E(_sS)(_Ra),_Rh=_Rg,_Ri=new T(function(){var _Rj=String(_Rh);return fromJSStr(_Rj);}),_=wMV(_Qz,_Ri),_Rk=jsFind(toJSStr(E(_kC)));if(!_Rk[0]){return new F(function(){return die(_PH);});}else{var _Rl=new T(function(){return B(_18(_Ri,_PN));}),_Rm=B(A(_h0,[_U,_7e,_Rk[1],_PL,_Rl,_])),_Rn=jsFind(toJSStr(E(_kD)));if(!_Rn[0]){return new F(function(){return die(_PK);});}else{var _Ro=new T(function(){return B(_18(_Ri,_PM));}),_Rp=B(A(_h0,[_U,_7e,_Rn[1],_PL,_Ro,_]));return new F(function(){return _p4(_QE,_Qs,_QF,_);});}}},_Rq=B(A(_dp,[_7f,_U,_n,_Qj[1],_cs,_R7,_])),_Rr=B(A(_dp,[_7f,_U,_n,_Qk[1],_cs,_Pz,_])),_Rs=function(_){var _Rt=jsFind(_Ql);if(!_Rt[0]){return new F(function(){return die(_Pg);});}else{var _Ru=jsFind(_Qo);if(!_Ru[0]){return new F(function(){return die(_Pj);});}else{var _Rv=B(A(_oq,[_U,_7e,_Rt[1],_kL,_])),_Rw=rMV(_Qu),_Rx=E(_Rw),_=wMV(_Qu,[0,_Rx[1],_Rx[2],_Rv,_Rx[4],_Rx[5],_Rx[6],_Rx[7],_Rx[8]]),_Ry=B(A(_oq,[_U,_7e,_Ru[1],_kL,_])),_Rz=_Ry,_RA=rMV(_Qu),_RB=E(_RA),_RC=new T(function(){return B(_Q7(_Ps,_3y,_Rz));}),_=wMV(_Qu,[0,_RB[1],_RB[2],_RB[3],_RB[4],_RB[5],_RB[6],_RB[7],_RC]),_RD=jsFind(_QW),_RE=_RD,_RF=new T(function(){if(!_RE[0]){return E(_sU);}else{return E(_RE[1]);}}),_RG=B(A(_oq,[_U,_7e,_RF,_kL,_])),_RH=_RG,_RI=jsFind(_QZ),_RJ=_RI,_RK=new T(function(){if(!_RJ[0]){return E(_sU);}else{return E(_RJ[1]);}}),_RL=B(A(_oq,[_U,_7e,_RK,_kL,_])),_RM=_RL,_RN=jsFind(_R2),_RO=_RN,_RP=new T(function(){if(!_RO[0]){return E(_sU);}else{return E(_RO[1]);}}),_RQ=B(A(_oq,[_U,_7e,_RP,_kL,_])),_RR=_RQ,_RS=jsQuerySelectorAll(_R5,"input[name=\'mount\']:checked");if(!_RS[0]){return new F(function(){return _qf(_);});}else{if(!E(_RS[2])[0]){var _RT=B(A(_oq,[_U,_7e,_RS[1],_kL,_])),_RU=_RT,_RV=rMV(_Qu),_RW=E(_RV),_RX=new T(function(){var _RY=B(_Pk(B(_ul(_J7,_RU))));if(!_RY[0]){return E(_td);}else{if(!E(_RY[2])[0]){return E(_RY[1]);}else{return E(_tf);}}}),_RZ=new T(function(){var _S0=B(_Pk(B(_ul(_OY,_RR))));if(!_S0[0]){return E(_J8);}else{if(!E(_S0[2])[0]){return E(_S0[1]);}else{return E(_J9);}}}),_S1=new T(function(){var _S2=B(_Pk(B(_ul(_OY,_RM))));if(!_S2[0]){return E(_J8);}else{if(!E(_S2[2])[0]){return E(_S2[1]);}else{return E(_J9);}}}),_S3=new T(function(){var _S4=B(_Pk(B(_ul(_OY,_RH))));if(!_S4[0]){return E(_J8);}else{if(!E(_S4[2])[0]){return E(_S4[1]);}else{return E(_J9);}}}),_=wMV(_Qu,[0,_RW[1],_RW[2],_RW[3],_S3,_S1,_RZ,_RX,_RW[8]]);return new F(function(){return _p4(_QE,_Qs,_QF,_);});}else{return new F(function(){return _qf(_);});}}}}},_S5=function(_S6,_){return new F(function(){return _Rs(_);});},_S7=function(_S8,_){while(1){var _S9=E(_S8);if(!_S9[0]){var _Sa=B(A(_dp,[_7f,_U,_n,_Qn,_cs,_S5,_])),_Sb=B(A(_dp,[_7f,_U,_n,_Qq,_cs,_S5,_])),_Sc=B(A(_dp,[_7f,_U,_n,_QY,_cs,_S5,_])),_Sd=B(A(_dp,[_7f,_U,_n,_R1,_cs,_S5,_])),_Se=B(A(_dp,[_7f,_U,_n,_R4,_cs,_S5,_]));return _9;}else{var _Sf=B(A(_dp,[_7f,_U,_n,_S9[1],_cs,_S5,_]));_S8=_S9[2];continue;}}},_Sg=B(_S7(_R6,_)),_Sh=B(A(_dp,[_7f,_U,_P,_Qn,_qg,_S5,_])),_Si=B(A(_dp,[_7f,_U,_P,_Qq,_qg,_S5,_])),_Sj=B(A(_dp,[_7f,_U,_P,_QY,_qg,_S5,_])),_Sk=B(A(_dp,[_7f,_U,_P,_R1,_qg,_S5,_])),_Sl=B(A(_dp,[_7f,_U,_P,_R4,_qg,_S5,_]));return new F(function(){return _p4(_QE,_Qs,_QF,_);});}}}}}}}}}},_Sm=function(_){return new F(function(){return _Qi(_);});};
var hasteMain = function() {B(A(_Sm, [0]));};window.onload = hasteMain;