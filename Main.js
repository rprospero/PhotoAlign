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

var _0="src",_1=function(_2){return E(E(_2)[2]);},_3=function(_4,_5){var _6=function(_){var _7=jsCreateElem("img"),_8=jsSet(_7,E(_0),toJSStr(E(_5)));return _7;};return new F(function(){return A(_1,[_4,_6]);});},_9=0,_a=function(_){return _9;},_b=function(_c,_d,_){return new F(function(){return _a(_);});},_e="scroll",_f="submit",_g="blur",_h="focus",_i="change",_j="unload",_k="load",_l=function(_m){switch(E(_m)){case 0:return E(_k);case 1:return E(_j);case 2:return E(_i);case 3:return E(_h);case 4:return E(_g);case 5:return E(_f);default:return E(_e);}},_n=[0,_l,_b],_o=function(_p,_){return [1,_p];},_q=function(_r){return E(_r);},_s=[0,_q,_o],_t=function(_u){return E(E(_u)[1]);},_v=function(_w,_x){return (!B(A(_t,[_y,_w,_x])))?true:false;},_z=function(_A,_B){var _C=strEq(E(_A),E(_B));return (E(_C)==0)?false:true;},_D=function(_E,_F){return new F(function(){return _z(_E,_F);});},_y=new T(function(){return [0,_D,_v];}),_G=function(_H,_I){var _J=E(_H);if(!_J[0]){return E(_I);}else{var _K=_J[2],_L=new T(function(){return B(_G(_K,_I));});return [1,_J[1],_L];}},_M=new T(function(){return B(unCStr("!!: negative index"));}),_N=new T(function(){return B(unCStr("Prelude."));}),_O=new T(function(){return B(_G(_N,_M));}),_P=new T(function(){return B(err(_O));}),_Q=new T(function(){return B(unCStr("!!: index too large"));}),_R=new T(function(){return B(_G(_N,_Q));}),_S=new T(function(){return B(err(_R));}),_T=function(_U,_V){while(1){var _W=E(_U);if(!_W[0]){return E(_S);}else{var _X=E(_V);if(!_X){return E(_W[1]);}else{_U=_W[2];_V=_X-1|0;continue;}}}},_Y=function(_Z,_10){if(_10>=0){return new F(function(){return _T(_Z,_10);});}else{return E(_P);}},_11=new T(function(){return B(unCStr(": empty list"));}),_12=function(_13){var _14=new T(function(){return B(_G(_13,_11));},1);return new F(function(){return err(B(_G(_N,_14)));});},_15=new T(function(){return B(unCStr("head"));}),_16=new T(function(){return B(_12(_15));}),_17=function(_18){var _19=E(_18);if(_19[0]==3){var _1a=E(_19[1]);if(!_1a[0]){return E(_16);}else{var _1b=E(_1a[1]);if(!_1b[0]){var _1c=B(_Y(_1a,1));return (_1c[0]==0)?[1,[0,_1b[1],_1c[1]]]:[0];}else{return [0];}}}else{return [0];}},_1d=function(_1e,_1f){var _1g=E(_1f);if(!_1g[0]){return [0];}else{var _1h=_1g[1],_1i=_1g[2],_1j=new T(function(){return B(_1d(_1e,_1i));}),_1k=new T(function(){return B(A(_1e,[_1h]));});return [1,_1k,_1j];}},_1l=function(_1m){var _1n=E(_1m);if(_1n[0]==3){var _1o=B(_1d(_17,_1n[1]));if(!_1o[0]){return E(_16);}else{var _1p=E(_1o[1]);if(!_1p[0]){return [0];}else{var _1q=B(_Y(_1o,1));if(!_1q[0]){return [0];}else{var _1r=B(_Y(_1o,2));if(!_1r[0]){return [0];}else{var _1s=B(_Y(_1o,3));return (_1s[0]==0)?[0]:[1,[0,_1p[1],_1q[1],_1r[1],_1s[1]]];}}}}}else{return [0];}},_1t="box",_1u="mouse",_1v="corner",_1w="Dragging",_1x=[0],_1y=[1,_1x],_1z="Free",_1A="state",_1B=1,_1C=[1,_1B],_1D=0,_1E=[1,_1D],_1F=3,_1G=[1,_1F],_1H=2,_1I=[1,_1H],_1J=new T(function(){return B(unCStr("SW"));}),_1K=new T(function(){return B(unCStr("SE"));}),_1L=new T(function(){return B(unCStr("NW"));}),_1M=new T(function(){return B(unCStr("NE"));}),_1N=function(_1O,_1P){while(1){var _1Q=E(_1O);if(!_1Q[0]){return (E(_1P)[0]==0)?true:false;}else{var _1R=E(_1P);if(!_1R[0]){return false;}else{if(E(_1Q[1])!=E(_1R[1])){return false;}else{_1O=_1Q[2];_1P=_1R[2];continue;}}}}},_1S=function(_1T){var _1U=E(_1T);if(_1U[0]==1){var _1V=fromJSStr(_1U[1]);return (!B(_1N(_1V,_1M)))?(!B(_1N(_1V,_1L)))?(!B(_1N(_1V,_1K)))?(!B(_1N(_1V,_1J)))?[0]:E(_1I):E(_1G):E(_1E):E(_1C);}else{return [0];}},_1W=function(_1X,_1Y,_1Z){while(1){var _20=E(_1Z);if(!_20[0]){return [0];}else{var _21=E(_20[1]);if(!B(A(_t,[_1X,_1Y,_21[1]]))){_1Z=_20[2];continue;}else{return [1,_21[2]];}}}},_22=function(_23){var _24=E(_23);if(_24[0]==4){var _25=_24[1],_26=B(_1W(_y,_1A,_25));if(!_26[0]){return [0];}else{var _27=E(_26[1]);if(_27[0]==1){var _28=_27[1],_29=strEq(_28,E(_1z));if(!E(_29)){var _2a=strEq(_28,E(_1w));if(!E(_2a)){return [0];}else{var _2b=B(_1W(_y,_1v,_25));if(!_2b[0]){return [0];}else{var _2c=B(_1S(_2b[1]));return (_2c[0]==0)?[0]:[1,[1,_2c[1]]];}}}else{return E(_1y);}}else{return [0];}}}else{return [0];}},_2d=function(_2e){var _2f=E(_2e);if(_2f[0]==4){var _2g=_2f[1],_2h=B(_1W(_y,_1u,_2g));if(!_2h[0]){return [0];}else{var _2i=B(_22(_2h[1]));if(!_2i[0]){return [0];}else{var _2j=B(_1W(_y,_1t,_2g));if(!_2j[0]){return [0];}else{var _2k=B(_1l(_2j[1]));return (_2k[0]==0)?[0]:[1,[0,_2i[1],_2k[1]]];}}}}else{return [0];}},_2l=1,_2m=[1,_2l],_2n=0,_2o=[1,_2n],_2p=new T(function(){return B(unCStr("Free"));}),_2q=new T(function(){return B(unCStr("Dragging"));}),_2r=function(_2s){var _2t=E(_2s);if(_2t[0]==1){var _2u=fromJSStr(_2t[1]);return (!B(_1N(_2u,_2q)))?(!B(_1N(_2u,_2p)))?[0]:E(_2o):E(_2m);}else{return [0];}},_2v="title",_2w="points",_2x=function(_2y){var _2z=E(_2y);if(_2z[0]==4){var _2A=_2z[1],_2B=B(_1W(_y,_2w,_2A));if(!_2B[0]){return [0];}else{var _2C=E(_2B[1]);if(_2C[0]==3){var _2D=E(_2C[1]);if(!_2D[0]){return E(_16);}else{var _2E=E(_2D[1]);if(_2E[0]==3){var _2F=E(_2E[1]);if(!_2F[0]){return E(_16);}else{var _2G=E(_2F[1]);if(!_2G[0]){var _2H=B(_Y(_2F,1));if(!_2H[0]){var _2I=B(_Y(_2D,1));if(_2I[0]==3){var _2J=E(_2I[1]);if(!_2J[0]){return E(_16);}else{var _2K=E(_2J[1]);if(!_2K[0]){var _2L=B(_Y(_2J,1));if(!_2L[0]){var _2M=B(_1W(_y,_2v,_2A));if(!_2M[0]){return [0];}else{var _2N=E(_2M[1]);if(_2N[0]==1){var _2O=_2N[1],_2P=new T(function(){return fromJSStr(_2O);});return [1,[0,[0,_2G[1],_2H[1]],[0,_2K[1],_2L[1]],_2P]];}else{return [0];}}}else{return [0];}}else{return [0];}}}else{return [0];}}else{return [0];}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}},_2Q=function(_2R){return [0,E(_2R)];},_2S=[0],_2T=function(_2U){var _2V=new T(function(){var _2W=E(E(_2U)[2]),_2X=_2W[1],_2Y=_2W[2],_2Z=new T(function(){return B(_2Q(_2Y));}),_30=new T(function(){return B(_2Q(_2X));});return [3,[1,_30,[1,_2Z,_2S]]];}),_31=new T(function(){var _32=E(E(_2U)[1]),_33=_32[1],_34=_32[2],_35=new T(function(){return B(_2Q(_34));}),_36=new T(function(){return B(_2Q(_33));});return [3,[1,_36,[1,_35,_2S]]];}),_37=new T(function(){return [1,toJSStr(E(E(_2U)[3]))];});return [1,[0,_2v,_37],[1,[0,_2w,[3,[1,_31,[1,_2V,_2S]]]],_2S]];},_38=function(_39){return [4,E(B(_2T(_39)))];},_3a=[0,_38,_2x],_3b="scans",_3c="mouse",_3d=[1,_2S],_3e=function(_3f){return E(E(_3f)[2]);},_3g=function(_3h,_3i){var _3j=E(_3i);if(_3j[0]==3){var _3k=new T(function(){return B(_3e(_3h));}),_3l=function(_3m){var _3n=E(_3m);if(!_3n[0]){return E(_3d);}else{var _3o=B(A(_3k,[_3n[1]]));if(!_3o[0]){return [0];}else{var _3p=B(_3l(_3n[2]));return (_3p[0]==0)?[0]:[1,[1,_3o[1],_3p[1]]];}}};return new F(function(){return _3l(_3j[1]);});}else{return [0];}},_3q=function(_3r){var _3s=E(_3r);if(_3s[0]==4){var _3t=_3s[1],_3u=B(_1W(_y,_3c,_3t));if(!_3u[0]){return [0];}else{var _3v=B(_2r(_3u[1]));if(!_3v[0]){return [0];}else{var _3w=B(_1W(_y,_3b,_3t));if(!_3w[0]){return [0];}else{var _3x=B(_3g(_3a,_3w[1]));return (_3x[0]==0)?[0]:[1,[0,_3v[1],_3x[1]]];}}}}else{return [0];}},_3y="scans",_3z="calib",_3A=function(_3B){var _3C=E(_3B);if(_3C[0]==4){var _3D=_3C[1],_3E=B(_1W(_y,_3z,_3D));if(!_3E[0]){return [0];}else{var _3F=B(_2d(_3E[1]));if(!_3F[0]){return [0];}else{var _3G=B(_1W(_y,_3y,_3D));if(!_3G[0]){return [0];}else{var _3H=B(_3q(_3G[1]));return (_3H[0]==0)?[0]:[1,[0,_3F[1],_3H[1]]];}}}}else{return [0];}},_3I=function(_3J,_3K,_){var _3L=B(A(_3J,[_])),_3M=B(A(_3K,[_]));return _3L;},_3N=function(_3O,_3P,_){var _3Q=B(A(_3O,[_])),_3R=_3Q,_3S=B(A(_3P,[_])),_3T=_3S;return new T(function(){return B(A(_3R,[_3T]));});},_3U=function(_3V,_3W,_){var _3X=B(A(_3W,[_]));return _3V;},_3Y=function(_3Z,_40,_){var _41=B(A(_40,[_])),_42=_41;return new T(function(){return B(A(_3Z,[_42]));});},_43=[0,_3Y,_3U],_44=function(_45,_){return _45;},_46=function(_47,_48,_){var _49=B(A(_47,[_]));return new F(function(){return A(_48,[_]);});},_4a=[0,_43,_44,_3N,_46,_3I],_4b=function(_4c,_4d,_){var _4e=B(A(_4c,[_]));return new F(function(){return A(_4d,[_4e,_]);});},_4f=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_4g=new T(function(){return B(unCStr("base"));}),_4h=new T(function(){return B(unCStr("IOException"));}),_4i=new T(function(){var _4j=hs_wordToWord64(4053623282),_4k=hs_wordToWord64(3693590983);return [0,_4j,_4k,[0,_4j,_4k,_4g,_4f,_4h],_2S,_2S];}),_4l=function(_4m){return E(_4i);},_4n=function(_4o){return E(E(_4o)[1]);},_4p=function(_4q,_4r,_4s){var _4t=B(A(_4q,[_])),_4u=B(A(_4r,[_])),_4v=hs_eqWord64(_4t[1],_4u[1]);if(!_4v){return [0];}else{var _4w=hs_eqWord64(_4t[2],_4u[2]);return (!_4w)?[0]:[1,_4s];}},_4x=function(_4y){var _4z=E(_4y);return new F(function(){return _4p(B(_4n(_4z[1])),_4l,_4z[2]);});},_4A=new T(function(){return B(unCStr(": "));}),_4B=new T(function(){return B(unCStr(")"));}),_4C=new T(function(){return B(unCStr(" ("));}),_4D=new T(function(){return B(unCStr("interrupted"));}),_4E=new T(function(){return B(unCStr("system error"));}),_4F=new T(function(){return B(unCStr("unsatisified constraints"));}),_4G=new T(function(){return B(unCStr("user error"));}),_4H=new T(function(){return B(unCStr("permission denied"));}),_4I=new T(function(){return B(unCStr("illegal operation"));}),_4J=new T(function(){return B(unCStr("end of file"));}),_4K=new T(function(){return B(unCStr("resource exhausted"));}),_4L=new T(function(){return B(unCStr("resource busy"));}),_4M=new T(function(){return B(unCStr("does not exist"));}),_4N=new T(function(){return B(unCStr("already exists"));}),_4O=new T(function(){return B(unCStr("resource vanished"));}),_4P=new T(function(){return B(unCStr("timeout"));}),_4Q=new T(function(){return B(unCStr("unsupported operation"));}),_4R=new T(function(){return B(unCStr("hardware fault"));}),_4S=new T(function(){return B(unCStr("inappropriate type"));}),_4T=new T(function(){return B(unCStr("invalid argument"));}),_4U=new T(function(){return B(unCStr("failed"));}),_4V=new T(function(){return B(unCStr("protocol error"));}),_4W=function(_4X,_4Y){switch(E(_4X)){case 0:return new F(function(){return _G(_4N,_4Y);});break;case 1:return new F(function(){return _G(_4M,_4Y);});break;case 2:return new F(function(){return _G(_4L,_4Y);});break;case 3:return new F(function(){return _G(_4K,_4Y);});break;case 4:return new F(function(){return _G(_4J,_4Y);});break;case 5:return new F(function(){return _G(_4I,_4Y);});break;case 6:return new F(function(){return _G(_4H,_4Y);});break;case 7:return new F(function(){return _G(_4G,_4Y);});break;case 8:return new F(function(){return _G(_4F,_4Y);});break;case 9:return new F(function(){return _G(_4E,_4Y);});break;case 10:return new F(function(){return _G(_4V,_4Y);});break;case 11:return new F(function(){return _G(_4U,_4Y);});break;case 12:return new F(function(){return _G(_4T,_4Y);});break;case 13:return new F(function(){return _G(_4S,_4Y);});break;case 14:return new F(function(){return _G(_4R,_4Y);});break;case 15:return new F(function(){return _G(_4Q,_4Y);});break;case 16:return new F(function(){return _G(_4P,_4Y);});break;case 17:return new F(function(){return _G(_4O,_4Y);});break;default:return new F(function(){return _G(_4D,_4Y);});}},_4Z=new T(function(){return B(unCStr("}"));}),_50=new T(function(){return B(unCStr("{handle: "));}),_51=function(_52,_53,_54,_55,_56,_57){var _58=new T(function(){var _59=new T(function(){var _5a=new T(function(){var _5b=E(_55);if(!_5b[0]){return E(_57);}else{var _5c=new T(function(){var _5d=new T(function(){return B(_G(_4B,_57));},1);return B(_G(_5b,_5d));},1);return B(_G(_4C,_5c));}},1);return B(_4W(_53,_5a));}),_5e=E(_54);if(!_5e[0]){return E(_59);}else{var _5f=new T(function(){return B(_G(_4A,_59));},1);return B(_G(_5e,_5f));}}),_5g=E(_56);if(!_5g[0]){var _5h=E(_52);if(!_5h[0]){return E(_58);}else{var _5i=E(_5h[1]);if(!_5i[0]){var _5j=_5i[1],_5k=new T(function(){var _5l=new T(function(){var _5m=new T(function(){return B(_G(_4A,_58));},1);return B(_G(_4Z,_5m));},1);return B(_G(_5j,_5l));},1);return new F(function(){return _G(_50,_5k);});}else{var _5n=_5i[1],_5o=new T(function(){var _5p=new T(function(){var _5q=new T(function(){return B(_G(_4A,_58));},1);return B(_G(_4Z,_5q));},1);return B(_G(_5n,_5p));},1);return new F(function(){return _G(_50,_5o);});}}}else{var _5r=new T(function(){return B(_G(_4A,_58));},1);return new F(function(){return _G(_5g[1],_5r);});}},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _51(_5u[1],_5u[2],_5u[3],_5u[4],_5u[6],_2S);});},_5v=function(_5w,_5x,_5y){var _5z=E(_5x);return new F(function(){return _51(_5z[1],_5z[2],_5z[3],_5z[4],_5z[6],_5y);});},_5A=function(_5B,_5C){var _5D=E(_5B);return new F(function(){return _51(_5D[1],_5D[2],_5D[3],_5D[4],_5D[6],_5C);});},_5E=44,_5F=93,_5G=91,_5H=function(_5I,_5J,_5K){var _5L=E(_5J);if(!_5L[0]){return new F(function(){return unAppCStr("[]",_5K);});}else{var _5M=_5L[1],_5N=_5L[2],_5O=new T(function(){var _5P=new T(function(){var _5Q=[1,_5F,_5K],_5R=function(_5S){var _5T=E(_5S);if(!_5T[0]){return E(_5Q);}else{var _5U=_5T[1],_5V=_5T[2],_5W=new T(function(){var _5X=new T(function(){return B(_5R(_5V));});return B(A(_5I,[_5U,_5X]));});return [1,_5E,_5W];}};return B(_5R(_5N));});return B(A(_5I,[_5M,_5P]));});return [1,_5G,_5O];}},_5Y=function(_5Z,_60){return new F(function(){return _5H(_5A,_5Z,_60);});},_61=[0,_5v,_5s,_5Y],_62=new T(function(){return [0,_4l,_61,_63,_4x,_5s];}),_63=function(_64){return [0,_62,_64];},_65=[0],_66=7,_67=function(_68){return [0,_65,_66,_2S,_68,_65,_65];},_69=function(_6a,_){var _6b=new T(function(){var _6c=new T(function(){return B(_67(_6a));});return B(_63(_6c));});return new F(function(){return die(_6b);});},_6d=[0,_4a,_4b,_46,_44,_69],_6e=[0,_6d,_q],_6f=[0,_6e,_44],_6g=function(_6h,_6i,_6j,_6k,_6l,_6m,_6n,_6o){if(_6h!=_6l){return false;}else{if(E(_6i)!=E(_6m)){return false;}else{var _6p=E(_6j),_6q=E(_6n);if(E(_6p[1])!=E(_6q[1])){return false;}else{if(E(_6p[2])!=E(_6q[2])){return false;}else{return new F(function(){return _1N(_6k,_6o);});}}}}},_6r=function(_6s,_6t){var _6u=E(_6s),_6v=E(_6u[1]),_6w=E(_6t),_6x=E(_6w[1]);return new F(function(){return _6g(E(_6v[1]),_6v[2],_6u[2],_6u[3],E(_6x[1]),_6x[2],_6w[2],_6w[3]);});},_6y="scans",_6z=[1,_6y,_2S],_6A="calib",_6B=[1,_6A,_6z],_6C=function(_6D){var _6E=E(_6D),_6F=_6E[1],_6G=_6E[2],_6H=new T(function(){return B(_2Q(_6G));}),_6I=new T(function(){return B(_2Q(_6F));});return [3,[1,_6I,[1,_6H,_2S]]];},_6J=new T(function(){return [1,"Dragging"];}),_6K=[0,_1A,_6J],_6L=new T(function(){return [1,"Free"];}),_6M="state",_6N=[0,_6M,_6L],_6O=[1,_6N,_2S],_6P=[4,E(_6O)],_6Q=function(_6R,_6S){switch(E(_6R)){case 0:return new F(function(){return _G(_1L,_6S);});break;case 1:return new F(function(){return _G(_1M,_6S);});break;case 2:return new F(function(){return _G(_1J,_6S);});break;default:return new F(function(){return _G(_1K,_6S);});}},_6T=function(_6U){return E(toJSStr(B(_6Q(_6U,_2S))));},_6V=function(_6W){return [1,B(_6T(_6W))];},_6X=function(_6Y){var _6Z=new T(function(){var _70=E(E(_6Y)[2]),_71=_70[1],_72=_70[2],_73=_70[3],_74=_70[4],_75=new T(function(){return B(_6C(_74));}),_76=new T(function(){return B(_6C(_73));}),_77=new T(function(){return B(_6C(_72));}),_78=new T(function(){return B(_6C(_71));});return [3,[1,_78,[1,_77,[1,_76,[1,_75,_2S]]]]];}),_79=new T(function(){var _7a=E(E(_6Y)[1]);if(!_7a[0]){return E(_6P);}else{var _7b=_7a[1],_7c=new T(function(){return B(_6V(_7b));});return [4,[1,_6K,[1,[0,_1v,_7c],_2S]]];}});return [1,[0,_1u,_79],[1,[0,_1t,_6Z],_2S]];},_7d="scans",_7e=[1,_7d,_2S],_7f="mouse",_7g=[1,_7f,_7e],_7h=function(_7i,_7j){var _7k=E(_7i);if(!_7k[0]){return [0];}else{var _7l=_7k[2],_7m=E(_7j);if(!_7m[0]){return [0];}else{var _7n=_7m[2],_7o=new T(function(){return B(_7h(_7l,_7n));});return [1,[0,_7k[1],_7m[1]],_7o];}}},_7p=function(_7q){var _7r=new T(function(){return [3,E(B(_1d(_38,E(_7q)[2])))];}),_7s=new T(function(){if(!E(E(_7q)[1])){return [1,toJSStr(E(_2p))];}else{return [1,toJSStr(E(_2q))];}});return new F(function(){return _7h(_7g,[1,_7s,[1,_7r,_2S]]);});},_7t=function(_7u){return [1,E(_7u)];},_7v="deltaZ",_7w="deltaY",_7x="deltaX",_7y=function(_7z,_7A){var _7B=jsShowI(_7z);return new F(function(){return _G(fromJSStr(_7B),_7A);});},_7C=41,_7D=40,_7E=function(_7F,_7G,_7H){if(_7G>=0){return new F(function(){return _7y(_7G,_7H);});}else{if(_7F<=6){return new F(function(){return _7y(_7G,_7H);});}else{var _7I=new T(function(){var _7J=jsShowI(_7G);return B(_G(fromJSStr(_7J),[1,_7C,_7H]));});return [1,_7D,_7I];}}},_7K=new T(function(){return B(unCStr(")"));}),_7L=new T(function(){return B(_7E(0,2,_7K));}),_7M=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_7L));}),_7N=function(_7O){var _7P=new T(function(){return B(_7E(0,_7O,_7M));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_7P)));});},_7Q=function(_7R,_){return new T(function(){var _7S=Number(E(_7R)),_7T=jsTrunc(_7S);if(_7T<0){return B(_7N(_7T));}else{if(_7T>2){return B(_7N(_7T));}else{return _7T;}}});},_7U=0,_7V=[0,_7U,_7U,_7U],_7W="button",_7X=new T(function(){return jsGetMouseCoords;}),_7Y=function(_7Z,_){var _80=E(_7Z);if(!_80[0]){return _2S;}else{var _81=_80[1],_82=B(_7Y(_80[2],_)),_83=new T(function(){var _84=Number(E(_81));return jsTrunc(_84);});return [1,_83,_82];}},_85=function(_86,_){var _87=__arr2lst(0,_86);return new F(function(){return _7Y(_87,_);});},_88=function(_89,_){return new F(function(){return _85(E(_89),_);});},_8a=function(_8b,_){return new T(function(){var _8c=Number(E(_8b));return jsTrunc(_8c);});},_8d=[0,_8a,_88],_8e=function(_8f,_){var _8g=E(_8f);if(!_8g[0]){return _2S;}else{var _8h=B(_8e(_8g[2],_));return [1,_8g[1],_8h];}},_8i=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_8j=[0,_65,_66,_2S,_8i,_65,_65],_8k=new T(function(){return B(_63(_8j));}),_8l=function(_){return new F(function(){return die(_8k);});},_8m=function(_8n){return E(E(_8n)[1]);},_8o=function(_8p,_8q,_8r,_){var _8s=__arr2lst(0,_8r),_8t=B(_8e(_8s,_)),_8u=E(_8t);if(!_8u[0]){return new F(function(){return _8l(_);});}else{var _8v=E(_8u[2]);if(!_8v[0]){return new F(function(){return _8l(_);});}else{if(!E(_8v[2])[0]){var _8w=B(A(_8m,[_8p,_8u[1],_])),_8x=B(A(_8m,[_8q,_8v[1],_]));return [0,_8w,_8x];}else{return new F(function(){return _8l(_);});}}}},_8y=function(_){return new F(function(){return __jsNull();});},_8z=function(_8A){var _8B=B(A(_8A,[_]));return E(_8B);},_8C=new T(function(){return B(_8z(_8y));}),_8D=new T(function(){return E(_8C);}),_8E=function(_8F,_8G,_){if(E(_8F)==7){var _8H=E(_7X)(_8G),_8I=B(_8o(_8d,_8d,_8H,_)),_8J=_8I,_8K=_8G[E(_7x)],_8L=_8K,_8M=_8G[E(_7w)],_8N=_8M,_8O=_8G[E(_7v)],_8P=_8O;return new T(function(){return [0,E(_8J),E(_65),[0,_8L,_8N,_8P]];});}else{var _8Q=E(_7X)(_8G),_8R=B(_8o(_8d,_8d,_8Q,_)),_8S=_8R,_8T=_8G[E(_7W)],_8U=__eq(_8T,E(_8D));if(!E(_8U)){var _8V=B(_7Q(_8T,_)),_8W=_8V;return new T(function(){return [0,E(_8S),[1,_8W],E(_7V)];});}else{return new T(function(){return [0,E(_8S),E(_65),E(_7V)];});}}},_8X=function(_8Y,_8Z,_){return new F(function(){return _8E(_8Y,E(_8Z),_);});},_90="mouseout",_91="mouseover",_92="mousemove",_93="mouseup",_94="mousedown",_95="dblclick",_96="click",_97="wheel",_98=function(_99){switch(E(_99)){case 0:return E(_96);case 1:return E(_95);case 2:return E(_94);case 3:return E(_93);case 4:return E(_92);case 5:return E(_91);case 6:return E(_90);default:return E(_97);}},_9a=[0,_98,_8X],_9b=function(_){return new F(function(){return jsCreateElem("th");});},_9c=function(_9d,_9e){var _9f=function(_){return new F(function(){return jsCreateTextNode(toJSStr(E(_9e)));});};return new F(function(){return A(_1,[_9d,_9f]);});},_9g=function(_9h){return E(E(_9h)[1]);},_9i=function(_9j){return E(E(_9j)[3]);},_9k=function(_9l){return E(E(_9l)[2]);},_9m=function(_9n){return E(E(_9n)[4]);},_9o=function(_9p){return E(E(_9p)[1]);},_9q=function(_9r,_9s,_9t,_9u){var _9v=new T(function(){return B(A(_9o,[_9r,_9t]));}),_9w=function(_9x,_){var _9y=E(_9x);if(!_9y[0]){return _9;}else{var _9z=E(_9v),_9A=jsAppendChild(E(_9y[1]),_9z),_9B=_9y[2],_=_;while(1){var _9C=E(_9B);if(!_9C[0]){return _9;}else{var _9D=jsAppendChild(E(_9C[1]),_9z);_9B=_9C[2];continue;}}}},_9E=function(_9F,_){while(1){var _9G=(function(_9H,_){var _9I=E(_9H);if(!_9I[0]){return _9;}else{var _9J=_9I[2],_9K=E(_9I[1]);if(!_9K[0]){var _9L=_9K[2],_9M=E(_9K[1]);switch(_9M[0]){case 0:var _9N=E(_9v),_9O=jsSet(_9N,_9M[1],_9L),_9P=_9J,_=_;while(1){var _9Q=E(_9P);if(!_9Q[0]){return _9;}else{var _9R=_9Q[2],_9S=E(_9Q[1]);if(!_9S[0]){var _9T=_9S[2],_9U=E(_9S[1]);switch(_9U[0]){case 0:var _9V=jsSet(_9N,_9U[1],_9T);_9P=_9R;continue;case 1:var _9W=jsSetStyle(_9N,_9U[1],_9T);_9P=_9R;continue;default:var _9X=jsSetAttr(_9N,_9U[1],_9T);_9P=_9R;continue;}}else{var _9Y=B(_9w(_9S[1],_));_9P=_9R;continue;}}}break;case 1:var _9Z=E(_9v),_a0=jsSetStyle(_9Z,_9M[1],_9L),_a1=_9J,_=_;while(1){var _a2=E(_a1);if(!_a2[0]){return _9;}else{var _a3=_a2[2],_a4=E(_a2[1]);if(!_a4[0]){var _a5=_a4[2],_a6=E(_a4[1]);switch(_a6[0]){case 0:var _a7=jsSet(_9Z,_a6[1],_a5);_a1=_a3;continue;case 1:var _a8=jsSetStyle(_9Z,_a6[1],_a5);_a1=_a3;continue;default:var _a9=jsSetAttr(_9Z,_a6[1],_a5);_a1=_a3;continue;}}else{var _aa=B(_9w(_a4[1],_));_a1=_a3;continue;}}}break;default:var _ab=E(_9v),_ac=jsSetAttr(_ab,_9M[1],_9L),_ad=_9J,_=_;while(1){var _ae=E(_ad);if(!_ae[0]){return _9;}else{var _af=_ae[2],_ag=E(_ae[1]);if(!_ag[0]){var _ah=_ag[2],_ai=E(_ag[1]);switch(_ai[0]){case 0:var _aj=jsSet(_ab,_ai[1],_ah);_ad=_af;continue;case 1:var _ak=jsSetStyle(_ab,_ai[1],_ah);_ad=_af;continue;default:var _al=jsSetAttr(_ab,_ai[1],_ah);_ad=_af;continue;}}else{var _am=B(_9w(_ag[1],_));_ad=_af;continue;}}}}}else{var _an=B(_9w(_9K[1],_));_9F=_9J;return null;}}})(_9F,_);if(_9G!=null){return _9G;}}},_ao=function(_){return new F(function(){return _9E(_9u,_);});};return new F(function(){return A(_1,[_9s,_ao]);});},_ap=function(_aq,_ar,_as,_at){var _au=B(_9g(_ar)),_av=function(_aw){var _ax=new T(function(){return B(A(_9m,[_au,_aw]));}),_ay=new T(function(){return B(_9q(_aq,_ar,_aw,_at));});return new F(function(){return A(_9i,[_au,_ay,_ax]);});};return new F(function(){return A(_9k,[_au,_as,_av]);});},_az=function(_aA,_){var _aB=E(_aA);if(!_aB[0]){return _2S;}else{var _aC=B(A(_9c,[_6e,_aB[1],_])),_aD=B(A(_ap,[_s,_6e,_9b,[1,[1,[1,_aC,_2S]],_2S],_])),_aE=B(_az(_aB[2],_));return [1,_aD,_aE];}},_aF=function(_aG,_aH,_){var _aI=B(A(_9c,[_6e,_aG,_])),_aJ=B(A(_ap,[_s,_6e,_9b,[1,[1,[1,_aI,_2S]],_2S],_])),_aK=B(_az(_aH,_));return [1,_aJ,_aK];},_aL=function(_){return new F(function(){return jsCreateElem("td");});},_aM=function(_aN,_aO,_){var _aP=jsShow(_aN),_aQ=jsCreateTextNode(toJSStr(fromJSStr(_aP))),_aR=B(A(_ap,[_s,_6e,_aL,[1,[1,[1,_aQ,_2S]],_2S],_])),_aS=B(A(_aO,[_]));return [1,_aR,_aS];},_aT=function(_aU,_aV){return [0,E(_aU),toJSStr(E(_aV))];},_aW=2,_aX=0,_aY=function(_){return new F(function(){return jsCreateElem("input");});},_aZ=new T(function(){return B(unCStr("x1"));}),_b0=function(_){return new F(function(){return jsCreateElem("tr");});},_b1=new T(function(){return B(unCStr("y1"));}),_b2=new T(function(){return B(unCStr("x2"));}),_b3=new T(function(){return B(unCStr("y2"));}),_b4=new T(function(){return B(unCStr("title"));}),_b5=new T(function(){return B(unCStr("Delete"));}),_b6=[1,_b5,_2S],_b7=[1,_b4,_b6],_b8=[1,_b3,_b7],_b9=[1,_b2,_b8],_ba=[1,_b1,_b9],_bb=function(_){return new F(function(){return jsCreateElem("span");});},_bc=new T(function(){return [0,[2,"class"],"glyphicon glyphicon-remove"];}),_bd=[1,_bc,_2S],_be=new T(function(){return B(_ap(_s,_6e,_bb,_bd));}),_bf=function(_bg,_){var _bh=E(_bg);if(!_bh[0]){return _2S;}else{var _bi=B(A(_ap,[_s,_6e,_aL,[1,[1,[1,_bh[1],_2S]],_2S],_])),_bj=B(_bf(_bh[2],_));return [1,_bi,_bj];}},_bk=function(_){return new F(function(){return jsCreateElem("button");});},_bl=new T(function(){return [2,"value"];}),_bm=new T(function(){return [0,[2,"type"],"text"];}),_bn=new T(function(){return [0,[2,"class"],"btn btn-danger"];}),_bo=function(_){return _2S;},_bp=function(_bq){return E(E(_bq)[1]);},_br=function(_bs){return E(E(_bs)[2]);},_bt=function(_bu){return E(E(_bu)[1]);},_bv=function(_){return new F(function(){return nMV(_65);});},_bw=new T(function(){return B(_8z(_bv));}),_bx=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_by=function(_bz){return E(E(_bz)[2]);},_bA=function(_bB,_bC,_bD,_bE,_bF,_bG){var _bH=B(_bp(_bB)),_bI=B(_9g(_bH)),_bJ=new T(function(){return B(_1(_bH));}),_bK=new T(function(){return B(_9m(_bI));}),_bL=new T(function(){return B(A(_9o,[_bC,_bE]));}),_bM=new T(function(){return B(A(_bt,[_bD,_bF]));}),_bN=function(_bO){return new F(function(){return A(_bK,[[0,_bM,_bL,_bO]]);});},_bP=function(_bQ){var _bR=new T(function(){var _bS=new T(function(){var _bT=E(_bL),_bU=E(_bM),_bV=E(_bQ),_bW=function(_bX,_){var _bY=B(A(_bV,[_bX,_]));return _8D;},_bZ=__createJSFunc(2,E(_bW)),_c0=_bZ,_c1=function(_){return new F(function(){return E(_bx)(_bT,_bU,_c0);});};return E(_c1);});return B(A(_bJ,[_bS]));});return new F(function(){return A(_9k,[_bI,_bR,_bN]);});},_c2=new T(function(){var _c3=new T(function(){return B(_1(_bH));}),_c4=function(_c5){var _c6=new T(function(){var _c7=function(_){var _=wMV(E(_bw),[1,_c5]);return new F(function(){return A(_br,[_bD,_bF,_c5,_]);});};return B(A(_c3,[_c7]));});return new F(function(){return A(_9k,[_bI,_c6,_bG]);});};return B(A(_by,[_bB,_c4]));});return new F(function(){return A(_9k,[_bI,_c2,_bP]);});},_c8=function(_c9,_ca){while(1){var _cb=E(_c9);if(!_cb[0]){return E(_ca);}else{_c9=_cb[2];var _cc=[1,_cb[1],_ca];_ca=_cc;continue;}}},_cd=function(_ce,_cf,_cg,_ch,_){var _ci=jsClearChildren(_ch),_cj=B(_aF(_aZ,_ba,_)),_ck=_cj,_cl=new T(function(){return B(_7t(_ck));}),_cm=B(A(_ap,[_s,_6e,_b0,[1,_cl,_2S],_])),_cn=jsAppendChild(E(_cm),_ch),_co=function(_cp,_){var _cq=E(_cp);if(!_cq[0]){return _2S;}else{var _cr=E(_cq[1]),_cs=_cr[3],_ct=E(_cr[1]),_cu=_ct[2],_cv=E(_cr[2]),_cw=_cv[1],_cx=_cv[2],_cy=function(_){var _cz=function(_){var _cA=function(_){return new F(function(){return _aM(E(_cx)*25/400,_bo,_);});};return new F(function(){return _aM(E(_cw)*25/400,_cA,_);});};return new F(function(){return _aM(E(_cu)*25/400,_cz,_);});},_cB=B(_aM(E(_ct[1])*25/400,_cy,_)),_cC=B(_bf(_cB,_)),_cD=_cC,_cE=new T(function(){return B(_7t(_cD));}),_cF=B(A(_ap,[_s,_6e,_b0,[1,_cE,_2S],_])),_cG=new T(function(){return B(_aT(_bl,_cs));}),_cH=B(A(_ap,[_s,_6e,_aY,[1,_bm,[1,_cG,_2S]],_])),_cI=_cH,_cJ=B(A(_be,[_])),_cK=B(A(_ap,[_s,_6e,_bk,[1,_bn,[1,[1,[1,_cJ,_2S]],_2S]],_])),_cL=B(A(_ap,[_s,_6e,_aL,[1,[1,[1,_cI,_2S]],_2S],_])),_cM=E(_cF),_cN=jsAppendChild(E(_cL),_cM),_cO=E(_cK),_cP=jsAppendChild(_cO,_cM),_cQ=new T(function(){return B(A(_cf,[_cr]));}),_cR=function(_cS){return E(_cQ);},_cT=B(A(_bA,[_6f,_s,_9a,_cO,_aX,_cR,_])),_cU=new T(function(){return B(A(_ce,[_cI,_cr]));}),_cV=function(_cW){return E(_cU);},_cX=B(A(_bA,[_6f,_s,_n,_cI,_aW,_cV,_])),_cY=jsAppendChild(_cM,_ch),_cZ=B(_co(_cq[2],_));return [1,_9,_cZ];}},_d0=B(_co(B(_c8(E(_cg)[2],_2S)),_));return _9;},_d1=function(_d2,_d3,_d4,_d5,_){var _d6=jsPushState(_d5),_d7=jsScale(_d5,_d2,_d3),_d8=B(A(_d4,[_d5,_])),_d9=jsPopState(_d5);return _9;},_da=function(_db,_dc,_){var _dd=jsBeginPath(_dc),_de=B(A(_db,[_dc,_])),_df=jsStroke(_dc);return _9;},_dg=",",_dh="[",_di="]",_dj="{",_dk="}",_dl=":",_dm="\"",_dn="true",_do="false",_dp="null",_dq=function(_dr){return new F(function(){return jsStringify(E(_dr));});},_ds=function(_dt){return new F(function(){return _dq(_dt);});},_du=function(_dv,_dw){var _dx=E(_dw);switch(_dx[0]){case 0:var _dy=_dx[1],_dz=new T(function(){return jsShow(_dy);});return [0,_dz,_dv];case 1:var _dA=_dx[1],_dB=new T(function(){return jsStringify(_dA);});return [0,_dB,_dv];case 2:return (!E(_dx[1]))?[0,_do,_dv]:[0,_dn,_dv];case 3:var _dC=E(_dx[1]);if(!_dC[0]){return [0,_dh,[1,_di,_dv]];}else{var _dD=_dC[1],_dE=_dC[2],_dF=new T(function(){var _dG=new T(function(){var _dH=[1,_di,_dv],_dI=function(_dJ){var _dK=E(_dJ);if(!_dK[0]){return E(_dH);}else{var _dL=_dK[1],_dM=_dK[2],_dN=new T(function(){var _dO=new T(function(){return B(_dI(_dM));}),_dP=B(_du(_dO,_dL));return [1,_dP[1],_dP[2]];});return [1,_dg,_dN];}};return B(_dI(_dE));}),_dQ=B(_du(_dG,_dD));return [1,_dQ[1],_dQ[2]];});return [0,_dh,_dF];}break;case 4:var _dR=E(_dx[1]);if(!_dR[0]){return [0,_dj,[1,_dk,_dv]];}else{var _dS=_dR[2],_dT=E(_dR[1]),_dU=_dT[1],_dV=_dT[2],_dW=new T(function(){var _dX=new T(function(){var _dY=[1,_dk,_dv],_dZ=function(_e0){var _e1=E(_e0);if(!_e1[0]){return E(_dY);}else{var _e2=_e1[2],_e3=E(_e1[1]),_e4=_e3[2],_e5=new T(function(){var _e6=new T(function(){return B(_dZ(_e2));}),_e7=B(_du(_e6,_e4));return [1,_e7[1],_e7[2]];});return [1,_dg,[1,_dm,[1,_e3[1],[1,_dm,[1,_dl,_e5]]]]];}};return B(_dZ(_dS));}),_e8=B(_du(_dX,_dV));return [1,_e8[1],_e8[2]];}),_e9=new T(function(){return B(_ds(_dU));});return [0,_dj,[1,_e9,[1,_dl,_dW]]];}break;default:return [0,_dp,_dv];}},_ea=new T(function(){return toJSStr(_2S);}),_eb=function(_ec){var _ed=B(_du(_2S,_ec)),_ee=jsCat([1,_ed[1],_ed[2]],E(_ea));return E(_ee);},_ef=function(_eg){var _eh=E(_eg);if(!_eh[0]){return [0];}else{var _ei=_eh[2],_ej=new T(function(){return B(_ef(_ei));},1);return new F(function(){return _G(_eh[1],_ej);});}},_ek=function(_el,_em){var _en=E(_em);if(!_en[0]){return [0];}else{var _eo=_en[2],_ep=new T(function(){return B(_ek(_el,_eo));});return [1,_el,[1,_en[1],_ep]];}},_eq=new T(function(){return B(unCStr("0"));}),_er=new T(function(){return B(unCStr("ccdtrans"));}),_es=new T(function(){return B(unCStr("1"));}),_et=[1,_es,_2S],_eu=[1,_es,_et],_ev=function(_ew){var _ex=_ew/0.1,_ey=_ex&4294967295;if(_ex>=_ey){return new F(function(){return _7E(0,_ey,_2S);});}else{return new F(function(){return _7E(0,_ey-1|0,_2S);});}},_ez=new T(function(){return B(_ev(0));}),_eA=new T(function(){return B(unCStr(" "));}),_eB=function(_eC,_eD,_eE,_eF,_eG,_eH){var _eI=new T(function(){var _eJ=new T(function(){var _eK=new T(function(){var _eL=jsShow(E(_eD)),_eM=new T(function(){var _eN=new T(function(){var _eO=new T(function(){var _eP=new T(function(){var _eQ=E(_eG)-E(_eF);if(!_eQ){return E(_ez);}else{if(_eQ<=0){return B(_ev( -_eQ));}else{return B(_ev(_eQ));}}}),_eR=new T(function(){var _eS=jsShow(E(_eG));return fromJSStr(_eS);}),_eT=new T(function(){var _eU=jsShow(E(_eF));return fromJSStr(_eU);});return B(_ek(_eA,[1,_eE,[1,_eT,[1,_eR,[1,_eP,[1,_eq,[1,_eH,_eu]]]]]]));});return B(_ef([1,_er,_eO]));});return B(unAppCStr("\r\n",_eN));},1);return B(_G(fromJSStr(_eL),_eM));});return B(unAppCStr(" ",_eK));},1);return B(_G(_eC,_eJ));});return new F(function(){return unAppCStr("umv ",_eI);});},_eV=new T(function(){return B(unCStr("sah"));}),_eW=new T(function(){return B(unCStr("sav"));}),_eX=function(_eY,_eZ,_f0,_f1,_f2){if(_eY!=_f0){var _f3=new T(function(){return E(_eZ)*25/400;},1);return new F(function(){return _eB(_eW,_f3,_eV,_eY*25/400,_f0*25/400,_f2);});}else{var _f4=new T(function(){return E(_f1)*25/400;}),_f5=new T(function(){return E(_eZ)*25/400;});return new F(function(){return _eB(_eV,_eY*25/400,_eW,_f5,_f4,_f2);});}},_f6=function(_f7){var _f8=E(_f7),_f9=E(_f8[1]),_fa=E(_f8[2]);return new F(function(){return _eX(E(_f9[1]),_f9[2],E(_fa[1]),_fa[2],_f8[3]);});},_fb=new T(function(){return B(unCStr("\r\n"));}),_fc=function(_fd){var _fe=B(_1d(_f6,B(_c8(_fd,_2S))));if(!_fe[0]){return [0];}else{var _ff=_fe[2],_fg=new T(function(){return B(_ek(_fb,_ff));});return new F(function(){return _ef([1,_fe[1],_fg]);});}},_fh=function(_fi,_fj){var _fk=function(_){return new F(function(){return jsFind(toJSStr(E(_fj)));});};return new F(function(){return A(_1,[_fi,_fk]);});},_fl=new T(function(){return encodeURIComponent;}),_fm=new T(function(){return B(unCStr("href"));}),_fn=new T(function(){return B(unCStr("data:text/plain;charset=utf-8,"));}),_fo=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:127:3-9"));}),_fp=[0,_65,_66,_2S,_fo,_65,_65],_fq=new T(function(){return B(_63(_fp));}),_fr=function(_fs,_ft,_fu,_fv,_fw){var _fx=function(_){var _fy=jsSetAttr(B(A(_9o,[_fs,_fu])),toJSStr(E(_fv)),toJSStr(E(_fw)));return _9;};return new F(function(){return A(_1,[_ft,_fx]);});},_fz=function(_fA,_fB,_){var _fC=B(A(_fh,[_6e,_fA,_])),_fD=E(_fC);if(!_fD[0]){return new F(function(){return die(_fq);});}else{var _fE=E(_fl)(toJSStr(_fB)),_fF=_fE,_fG=new T(function(){var _fH=new T(function(){var _fI=String(_fF);return fromJSStr(_fI);},1);return B(_G(_fn,_fH));});return new F(function(){return A(_fr,[_s,_6e,_fD[1],_fm,_fG,_]);});}},_fJ=function(_fK,_fL,_fM,_){var _fN=jsPushState(_fM),_fO=jsRotate(_fM,_fK),_fP=B(A(_fL,[_fM,_])),_fQ=jsPopState(_fM);return _9;},_fR=function(_fS,_fT,_fU,_fV,_){var _fW=jsPushState(_fV),_fX=jsTranslate(_fV,_fS,_fT),_fY=B(A(_fU,[_fV,_])),_fZ=jsPopState(_fV);return _9;},_g0=function(_g1,_g2){if(_g2<=0){var _g3=function(_g4){var _g5=function(_g6){var _g7=function(_g8){var _g9=function(_ga){var _gb=isDoubleNegativeZero(_g2),_gc=_gb,_gd=function(_ge){var _gf=E(_g1);if(!_gf){return (_g2>=0)?(E(_gc)==0)?E(_g2):3.141592653589793:3.141592653589793;}else{var _gg=E(_g2);return (_gg==0)?E(_gf):_gg+_gf;}};if(!E(_gc)){return new F(function(){return _gd(_);});}else{var _gh=E(_g1),_gi=isDoubleNegativeZero(_gh);if(!E(_gi)){return new F(function(){return _gd(_);});}else{return  -B(_g0( -_gh,_g2));}}};if(_g2>=0){return new F(function(){return _g9(_);});}else{var _gj=E(_g1),_gk=isDoubleNegativeZero(_gj);if(!E(_gk)){return new F(function(){return _g9(_);});}else{return  -B(_g0( -_gj,_g2));}}};if(_g2>0){return new F(function(){return _g7(_);});}else{var _gl=E(_g1);if(_gl>=0){return new F(function(){return _g7(_);});}else{return  -B(_g0( -_gl,_g2));}}};if(_g2>=0){return new F(function(){return _g5(_);});}else{var _gm=E(_g1);if(_gm<=0){return new F(function(){return _g5(_);});}else{return 3.141592653589793+Math.atan(_gm/_g2);}}};if(!E(_g2)){if(E(_g1)<=0){return new F(function(){return _g3(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _g3(_);});}}else{return new F(function(){return Math.atan(E(_g1)/_g2);});}},_gn=function(_go,_gp){return E(_go)-E(_gp);},_gq=function(_gr,_gs,_gt,_gu,_gv,_gw,_gx,_gy){var _gz=new T(function(){return B(_gn(_gu,_gs));}),_gA=new T(function(){return B(_gn(_gw,_gu));}),_gB=new T(function(){return B(_gn(_gy,_gw));}),_gC=new T(function(){return B(_gn(_gs,_gy));});return new F(function(){return Math.atan((Math.tan(B(_g0(_gz,_gt-_gr))-1.5707963267948966)+Math.tan(B(_g0(_gA,_gv-_gt)))+Math.tan(B(_g0(_gB,_gx-_gv))+1.5707963267948966)+Math.tan(B(_g0(_gC,_gr-_gx))-3.141592653589793))/4);});},_gD=function(_gE){return E(_gE)/2;},_gF=function(_gG,_gH,_gI,_){var _gJ=E(_gG);return new F(function(){return _fR(E(_gJ[1]),E(_gJ[2]),_gH,E(_gI),_);});},_gK=function(_gL,_gM){var _gN=new T(function(){var _gO=E(_gL),_gP=E(E(_gM)[2]),_gQ=E(_gP[1]),_gR=E(_gQ[1]),_gS=E(_gQ[2]),_gT=E(_gP[2]),_gU=E(_gT[1]),_gV=E(_gT[2]),_gW=E(_gP[3]),_gX=E(_gW[1]),_gY=E(_gW[2]),_gZ=E(_gP[4]),_h0=E(_gZ[1]),_h1=E(_gZ[2]);return Math.sqrt(E(_gO[1])*E(_gO[2])/(0.5*(_gR*_h1+_h0*_gY+_gX*_gS-_gR*_gY-_gX*_h1-_h0*_gS)+0.5*(_h0*_gY+_gX*_gV+_gU*_h1-_h0*_gV-_gU*_gY-_gX*_h1)));}),_h2=new T(function(){var _h3=E(_gL),_h4=_h3[1],_h5=_h3[2],_h6=new T(function(){return B(_gD(_h5));}),_h7=new T(function(){return B(_gD(_h4));});return [0,_h7,_h6];}),_h8=new T(function(){var _h9=E(E(_gM)[2]),_ha=E(_h9[1]),_hb=E(_h9[2]),_hc=E(_h9[3]),_hd=E(_h9[4]);return  -B(_gq(E(_ha[1]),_ha[2],E(_hb[1]),_hb[2],E(_hc[1]),_hc[2],E(_hd[1]),_hd[2]));}),_he=new T(function(){var _hf=E(E(_gM)[2]),_hg=E(_hf[1]),_hh=_hg[1],_hi=_hg[2],_hj=E(_hf[2]),_hk=_hj[1],_hl=_hj[2],_hm=E(_hf[3]),_hn=_hm[1],_ho=_hm[2],_hp=E(_hf[4]),_hq=_hp[1],_hr=_hp[2],_hs=new T(function(){return (E(_hi)+E(_hl)+E(_ho)+E(_hr))/4/(-1);}),_ht=new T(function(){return (E(_hh)+E(_hk)+E(_hn)+E(_hq))/4/(-1);});return [0,_ht,_hs];}),_hu=function(_hv,_hw,_){var _hx=E(_h2),_hy=function(_hz,_){var _hA=E(_gN),_hB=function(_hC,_){var _hD=function(_hE,_){return new F(function(){return _gF(_he,_hv,_hE,_);});};return new F(function(){return _fJ(E(_h8),_hD,E(_hC),_);});};return new F(function(){return _d1(_hA,_hA,_hB,E(_hz),_);});};return new F(function(){return _fR(E(_hx[1]),E(_hx[2]),_hy,E(_hw),_);});};return E(_hu);},_hF=function(_hG,_hH,_){var _hI=E(_hG);if(!_hI[0]){return _9;}else{var _hJ=E(_hI[1]),_hK=E(_hH),_hL=jsMoveTo(_hK,E(_hJ[1]),E(_hJ[2])),_hM=_hI[2],_=_;while(1){var _hN=E(_hM);if(!_hN[0]){return _9;}else{var _hO=E(_hN[1]),_hP=jsLineTo(_hK,E(_hO[1]),E(_hO[2]));_hM=_hN[2];continue;}}}},_hQ=function(_hR,_hS,_){var _hT=new T(function(){return E(E(_hR)[2]);}),_hU=new T(function(){return E(E(_hT)[1]);}),_hV=new T(function(){return E(E(_hT)[4]);}),_hW=new T(function(){return E(E(_hT)[3]);}),_hX=new T(function(){return E(E(_hT)[2]);});return new F(function(){return _hF([1,_hU,[1,_hX,[1,_hW,[1,_hV,[1,_hU,_2S]]]]],_hS,_);});},_hY=",",_hZ="rgba(",_i0=new T(function(){return toJSStr(_2S);}),_i1="rgb(",_i2=")",_i3=[1,_i2,_2S],_i4=function(_i5){var _i6=E(_i5);if(!_i6[0]){var _i7=_i6[1],_i8=_i6[2],_i9=_i6[3],_ia=new T(function(){return String(_i9);}),_ib=new T(function(){return String(_i8);}),_ic=new T(function(){return String(_i7);}),_id=jsCat([1,_i1,[1,_ic,[1,_hY,[1,_ib,[1,_hY,[1,_ia,_i3]]]]]],E(_i0));return E(_id);}else{var _ie=_i6[4],_if=_i6[1],_ig=_i6[2],_ih=_i6[3],_ii=new T(function(){return String(_ie);}),_ij=new T(function(){return String(_ih);}),_ik=new T(function(){return String(_ig);}),_il=new T(function(){return String(_if);}),_im=jsCat([1,_hZ,[1,_il,[1,_hY,[1,_ik,[1,_hY,[1,_ij,[1,_hY,[1,_ii,_i3]]]]]]]],E(_i0));return E(_im);}},_in="strokeStyle",_io="fillStyle",_ip=function(_iq,_ir){var _is=new T(function(){return B(_i4(_iq));}),_it=function(_iu,_){var _iv=E(_iu),_iw=E(_io),_ix=jsGet(_iv,_iw),_iy=E(_in),_iz=jsGet(_iv,_iy),_iA=E(_is),_iB=jsSet(_iv,_iw,_iA),_iC=jsSet(_iv,_iy,_iA),_iD=B(A(_ir,[_iv,_])),_iE=jsSet(_iv,_iw,_ix),_iF=jsSet(_iv,_iy,_iz);return _9;};return E(_it);},_iG=function(_iH,_iI,_iJ){var _iK=E(_iJ);if(!_iK[0]){return [0];}else{var _iL=_iK[1],_iM=_iK[2];if(!B(A(_iH,[_iI,_iL]))){var _iN=new T(function(){return B(_iG(_iH,_iI,_iM));});return [1,_iL,_iN];}else{return E(_iM);}}},_iO="lineWidth",_iP=function(_iQ,_iR){var _iS=new T(function(){return String(E(_iQ));}),_iT=function(_iU,_){var _iV=E(_iU),_iW=E(_iO),_iX=jsGet(_iV,_iW),_iY=jsSet(_iV,_iW,E(_iS)),_iZ=B(A(_iR,[_iV,_])),_j0=jsSet(_iV,_iW,_iX);return _9;};return E(_iT);},_j1=[0,255,0,255],_j2=1,_j3=900,_j4=[0,_j3,_j3],_j5=new T(function(){return B(unCStr("btn btn-primary"));}),_j6=new T(function(){return B(unCStr("class"));}),_j7=new T(function(){return B(unCStr("btn btn-primary disabled"));}),_j8=function(_j9,_){var _ja=jsHasCtx2D(_j9);if(!E(_ja)){return _65;}else{var _jb=jsGetCtx2D(_j9);return [1,[0,_jb,_j9]];}},_jc=function(_jd,_){return new F(function(){return _j8(E(_jd),_);});},_je=function(_jf,_jg){var _jh=function(_){var _ji=jsFind(toJSStr(E(_jg)));if(!_ji[0]){return _65;}else{return new F(function(){return _jc(_ji[1],_);});}};return new F(function(){return A(_1,[_jf,_jh]);});},_jj=new T(function(){return B(unCStr("aligned"));}),_jk=new T(function(){return B(_je(_6e,_jj));}),_jl=new T(function(){return B(unCStr("original"));}),_jm=new T(function(){return B(_je(_6e,_jl));}),_jn=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:105:3-8"));}),_jo=[0,_65,_66,_2S,_jn,_65,_65],_jp=new T(function(){return B(_63(_jo));}),_jq=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:89:3-10"));}),_jr=[0,_65,_66,_2S,_jq,_65,_65],_js=new T(function(){return B(_63(_jr));}),_jt=new T(function(){return B(unCStr("scans"));}),_ju=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:88:3-11"));}),_jv=[0,_65,_66,_2S,_ju,_65,_65],_jw=new T(function(){return B(_63(_jv));}),_jx=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:87:3-11"));}),_jy=[0,_65,_66,_2S,_jx,_65,_65],_jz=new T(function(){return B(_63(_jy));}),_jA=new T(function(){return B(unCStr("saveLink"));}),_jB=new T(function(){return B(unCStr("exportLink"));}),_jC=function(_jD,_jE,_){while(1){var _jF=E(_jD);if(!_jF[0]){return _9;}else{var _jG=E(_jF[1]),_jH=B(_hF([1,_jG[1],[1,_jG[2],_2S]],_jE,_));_jD=_jF[2];continue;}}},_jI=[0,255,0,255],_jJ=1,_jK=function(_jL){var _jM=new T(function(){var _jN=new T(function(){var _jO=E(_jL)[2];return function(_jP,_jQ){return new F(function(){return _jC(_jO,_jP,_jQ);});};}),_jR=function(_jS,_){return new F(function(){return _da(_jN,E(_jS),_);});};return B(_ip(_jI,_jR));});return new F(function(){return _iP(_jJ,_jM);});},_jT=function(_jU){while(1){var _jV=E(_jU);if(!_jV[0]){return true;}else{if(E(_jV[1])==32){return false;}else{_jU=_jV[2];continue;}}}},_jW=function(_jX,_jY){if(E(_jX)==32){return false;}else{return new F(function(){return _jT(_jY);});}},_jZ=function(_k0){while(1){var _k1=E(_k0);if(!_k1[0]){return true;}else{var _k2=E(_k1[1]);if(!_k2[0]){return false;}else{if(!B(_jW(_k2[1],_k2[2]))){return false;}else{_k0=_k1[2];continue;}}}}},_k3=function(_k4){return E(E(_k4)[3]);},_k5=function(_k6){return new F(function(){return fromJSStr(E(_k6));});},_k7=function(_k8,_k9,_ka,_kb){var _kc=function(_){return new F(function(){return jsGet(B(A(_9o,[_k8,_ka])),E(_kb));});};return new F(function(){return A(_1,[_k9,_kc]);});},_kd=function(_ke,_kf,_kg,_kh){var _ki=B(_9g(_kf)),_kj=new T(function(){return B(_9m(_ki));}),_kk=function(_kl){var _km=new T(function(){return B(_k5(_kl));});return new F(function(){return A(_kj,[_km]);});},_kn=new T(function(){var _ko=new T(function(){return toJSStr(E(_kh));});return B(_k7(_ke,_kf,_kg,_ko));});return new F(function(){return A(_9k,[_ki,_kn,_kk]);});},_kp=new T(function(){return B(unCStr("value"));}),_kq=function(_kr,_ks,_kt){var _ku=E(_kt);if(!_ku[0]){return [0];}else{var _kv=_ku[1],_kw=_ku[2];if(!B(A(_kr,[_kv]))){var _kx=new T(function(){return B(_kq(_kr,_ks,_kw));});return [1,_kv,_kx];}else{var _ky=new T(function(){return B(_kq(_kr,_ks,_kw));}),_kz=new T(function(){return B(A(_ks,[_kv]));});return [1,_kz,_ky];}}},_kA=function(_kB,_kC,_kD,_kE,_){var _kF=B(A(_kd,[_s,_6e,_kD,_kp,_])),_kG=_kF,_kH=E(_kC),_kI=rMV(_kH),_kJ=E(_kI),_kK=_kJ[2],_kL=new T(function(){var _kM=function(_kN){var _kO=E(_kN);return [0,_kO[1],_kO[2],_kG];},_kP=function(_kQ){return new F(function(){return _6r(_kQ,_kE);});};return B(_kq(_kP,_kM,_kK));}),_=wMV(_kH,[0,_kJ[1],_kL]);return new F(function(){return A(_kB,[_]);});},_kR=function(_kS,_kT,_kU,_){var _kV=rMV(_kT),_kW=_kV,_kX=E(_kS),_kY=_kX,_kZ=rMV(_kY),_l0=B(A(_jm,[_])),_l1=E(_l0);if(!_l1[0]){return new F(function(){return die(_jz);});}else{var _l2=_l1[1],_l3=B(A(_jk,[_])),_l4=E(_l3);if(!_l4[0]){return new F(function(){return die(_jw);});}else{var _l5=_l4[1],_l6=jsFind(toJSStr(E(_jt)));if(!_l6[0]){return new F(function(){return die(_js);});}else{var _l7=_l6[1],_l8=E(_jB),_l9=jsFind(toJSStr(_l8));if(!_l9[0]){return new F(function(){return die(_jp);});}else{var _la=_l9[1],_lb=E(_kZ),_lc=_lb[2],_ld=function(_){var _le=function(_lf,_){var _lg=rMV(_kY),_lh=E(_lg),_li=_lh[2],_lj=new T(function(){return B(_iG(_6r,_lf,_li));}),_=wMV(_kY,[0,_lh[1],_lj]);return new F(function(){return _kR(_kX,_kT,_kU,_);});},_lk=function(_){return new F(function(){return _kR(_kX,_kT,_kU,_);});},_ll=function(_lm,_ln,_){return new F(function(){return _kA(_lk,_kX,_lm,_ln,_);});},_lo=B(_cd(_ll,_le,_lb,E(_l7),_)),_lp=E(_kU),_lq=rMV(_lp),_lr=_lq,_ls=E(_l5),_lt=jsResetCanvas(_ls[2]),_lu=_ls[1],_lv=function(_lw,_){var _lx=jsDrawImage(E(_lw),E(_lr),0,0);return _9;},_ly=function(_lz,_){return new F(function(){return _d1(0.3,0.3,_lv,E(_lz),_);});},_lA=B(A(_gK,[_j4,_kW,_ly,_lu,_])),_lB=B(A(_jK,[_lb,_lu,_])),_lC=rMV(_lp),_lD=E(_l2),_lE=_lD[1],_lF=jsResetCanvas(_lD[2]),_lG=jsPushState(_lE),_lH=jsScale(_lE,0.3,0.3),_lI=jsDrawImage(_lE,E(_lC),0,0),_lJ=jsPopState(_lE),_lK=new T(function(){var _lL=function(_ln,_){return new F(function(){return _hQ(_kW,_ln,_);});},_lM=function(_lN,_){return new F(function(){return _da(_lL,E(_lN),_);});};return B(_ip(_j1,_lM));}),_lO=B(A(_iP,[_j2,_lK,_lE,_])),_lP=new T(function(){return B(_fc(_lc));},1),_lQ=B(_fz(_l8,_lP,_)),_lR=new T(function(){var _lS=new T(function(){return [4,E(B(_7p(_lb)))];}),_lT=new T(function(){return [4,E(B(_6X(_kW)))];});return fromJSStr(B(_eb([4,E(B(_7h(_6B,[1,_lT,[1,_lS,_2S]])))])));},1);return new F(function(){return _fz(_jA,_lR,_);});},_lU=E(_lc);if(!_lU[0]){var _lV=B(A(_fr,[_s,_6e,_la,_j6,_j7,_]));return new F(function(){return _ld(_);});}else{if(!B(_jZ(B(_1d(_k3,_lU))))){var _lW=B(A(_fr,[_s,_6e,_la,_j6,_j7,_]));return new F(function(){return _ld(_);});}else{var _lX=B(A(_fr,[_s,_6e,_la,_j6,_j5,_]));return new F(function(){return _ld(_);});}}}}}}},_lY=function(_lZ){return E(_lZ)[2];},_m0=function(_){return _65;},_m1=function(_m2,_){return new F(function(){return _m0(_);});},_m3=[0,_lY,_m1],_m4=function(_m5,_m6){while(1){var _m7=E(_m5);if(!_m7[0]){return E(_m6);}else{var _m8=_m7[2],_m9=E(_m7[1]);if(_m6>_m9){_m5=_m8;_m6=_m9;continue;}else{_m5=_m8;continue;}}}},_ma=function(_mb,_mc,_md){var _me=E(_mb);if(_md>_me){return new F(function(){return _m4(_mc,_me);});}else{return new F(function(){return _m4(_mc,_md);});}},_mf=2,_mg=4,_mh=3,_mi=function(_mj,_mk){var _ml=function(_mm,_mn){while(1){var _mo=(function(_mp,_mq){var _mr=E(_mp);if(!_mr[0]){return [0];}else{var _ms=_mr[2];if(!B(A(_mj,[_mr[1]]))){_mm=_ms;var _mt=_mq+1|0;_mn=_mt;return null;}else{var _mu=new T(function(){return B(_ml(_ms,_mq+1|0));});return [1,_mq,_mu];}}})(_mm,_mn);if(_mo!=null){return _mo;}}},_mv=B(_ml(_mk,0));return (_mv[0]==0)?[0]:[1,_mv[1]];},_mw=function(_mx){return E(_mx);},_my=function(_mz,_mA,_mB,_){var _mC=function(_mD,_){var _mE=E(_mz),_mF=rMV(_mE),_mG=E(E(_mF)[2]),_mH=_mG[1],_mI=_mG[2],_mJ=_mG[3],_mK=_mG[4],_mL=new T(function(){var _mM=new T(function(){var _mN=E(E(_mD)[1]),_mO=_mN[1],_mP=_mN[2],_mQ=new T(function(){return B(_mw(_mP));}),_mR=new T(function(){return B(_mw(_mO));});return [0,_mR,_mQ];}),_mS=new T(function(){var _mT=E(_mM),_mU=E(_mH);return Math.pow(E(_mT[1])-E(_mU[1]),2)+Math.pow(E(_mT[2])-E(_mU[2]),2);}),_mV=new T(function(){var _mW=E(_mM),_mX=E(_mI);return Math.pow(E(_mW[1])-E(_mX[1]),2)+Math.pow(E(_mW[2])-E(_mX[2]),2);}),_mY=new T(function(){var _mZ=E(_mM),_n0=E(_mJ);return Math.pow(E(_mZ[1])-E(_n0[1]),2)+Math.pow(E(_mZ[2])-E(_n0[2]),2);}),_n1=new T(function(){var _n2=E(_mM),_n3=E(_mK);return Math.pow(E(_n2[1])-E(_n3[1]),2)+Math.pow(E(_n2[2])-E(_n3[2]),2);}),_n4=[1,_mY,[1,_n1,_2S]],_n5=new T(function(){return B(_ma(_mV,_n4,E(_mS)));}),_n6=function(_n7){return E(_n5)==E(_n7);},_n8=B(_mi(_n6,[1,_mS,[1,_mV,_n4]]));if(!_n8[0]){return 3;}else{switch(E(_n8[1])){case 0:return 0;break;case 1:return 2;break;case 3:return 1;break;default:return 3;}}}),_=wMV(_mE,[0,[1,_mL],_mG]);return new F(function(){return A(_mB,[_]);});},_n9=B(A(_bA,[_6f,_m3,_9a,_mA,_mf,_mC,_])),_na=function(_nb,_){var _nc=E(_mz),_nd=rMV(_nc),_=wMV(_nc,[0,_1x,E(_nd)[2]]);return new F(function(){return A(_mB,[_]);});},_ne=B(A(_bA,[_6f,_m3,_9a,_mA,_mh,_na,_])),_nf=function(_ng,_){var _nh=E(_mz),_ni=rMV(_nh),_nj=E(_ni),_nk=_nj[2],_nl=E(_nj[1]);if(!_nl[0]){var _nm=E(_nj);}else{var _nn=new T(function(){var _no=E(E(_ng)[1]),_np=_no[1],_nq=_no[2],_nr=new T(function(){return B(_mw(_nq));}),_ns=new T(function(){return B(_mw(_np));});return [0,_ns,_nr];});switch(E(_nl[1])){case 0:var _nt=E(_nk),_nu=[0,_nl,[0,_nn,_nt[2],_nt[3],_nt[4]]];break;case 1:var _nv=E(_nk),_nu=[0,_nl,[0,_nv[1],_nv[2],_nv[3],_nn]];break;case 2:var _nw=E(_nk),_nu=[0,_nl,[0,_nw[1],_nn,_nw[3],_nw[4]]];break;default:var _nx=E(_nk),_nu=[0,_nl,[0,_nx[1],_nx[2],_nn,_nx[4]]];}var _nm=_nu;}var _=wMV(_nh,_nm);return new F(function(){return A(_mB,[_]);});},_ny=B(A(_bA,[_6f,_m3,_9a,_mA,_mg,_nf,_]));return _9;},_nz=function(_nA,_nB,_nC){if(!E(_nB)){return [0,_2n,_nC];}else{var _nD=E(_nC);if(!_nD[0]){return [0,_2l,_2S];}else{var _nE=_nD[1],_nF=new T(function(){return E(E(_nE)[1]);}),_nG=new T(function(){var _nH=E(_nF),_nI=_nH[1],_nJ=E(E(_nA)[1]),_nK=_nJ[1],_nL=E(_nH[2]),_nM=E(_nJ[2]),_nN=_nM-_nL;if(!_nN){var _nO=E(_nI),_nP=E(_nK),_nQ=_nP-_nO;if(!_nQ){return [0,_nP,_nL];}else{if(_nQ<=0){if(0<= -_nQ){return [0,_nP,_nL];}else{return [0,_nO,_nM];}}else{if(0<=_nQ){return [0,_nP,_nL];}else{return [0,_nO,_nM];}}}}else{if(_nN<=0){var _nR=E(_nI),_nS=E(_nK),_nT=_nS-_nR;if(!_nT){if( -_nN<=0){return [0,_nS,_nL];}else{return [0,_nR,_nM];}}else{if(_nT<=0){if( -_nN<= -_nT){return [0,_nS,_nL];}else{return [0,_nR,_nM];}}else{if( -_nN<=_nT){return [0,_nS,_nL];}else{return [0,_nR,_nM];}}}}else{var _nU=E(_nI),_nV=E(_nK),_nW=_nV-_nU;if(!_nW){return [0,_nU,_nM];}else{if(_nW<=0){if(_nN<= -_nW){return [0,_nV,_nL];}else{return [0,_nU,_nM];}}else{if(_nN<=_nW){return [0,_nV,_nL];}else{return [0,_nU,_nM];}}}}}});return [0,_2l,[1,[0,_nF,_nG,_2S],_nD[2]]];}}},_nX=function(_nY,_nZ,_o0,_){var _o1=function(_o2,_){var _o3=E(_nY),_o4=rMV(_o3),_o5=_o4,_o6=new T(function(){var _o7=E(E(_o2)[1]),_o8=_o7[1],_o9=_o7[2],_oa=new T(function(){return B(_mw(_o9));}),_ob=new T(function(){return B(_mw(_o8));});return [0,_ob,_oa];}),_oc=new T(function(){return E(E(_o5)[2]);}),_=wMV(_o3,[0,_2l,[1,[0,_o6,_o6,_2S],_oc]]);return new F(function(){return A(_o0,[_]);});},_od=B(A(_bA,[_6f,_m3,_9a,_nZ,_mf,_o1,_])),_oe=function(_of,_){var _og=E(_nY),_oh=rMV(_og),_oi=E(_oh),_=wMV(_og,[0,_2n,B(_nz(_of,_oi[1],_oi[2]))[2]]);return new F(function(){return A(_o0,[_]);});},_oj=B(A(_bA,[_6f,_m3,_9a,_nZ,_mh,_oe,_])),_ok=function(_ol,_){var _om=E(_nY),_on=rMV(_om),_oo=E(_on),_op=B(_nz(_ol,_oo[1],_oo[2])),_=wMV(_om,[0,_op[1],_op[2]]);return new F(function(){return A(_o0,[_]);});},_oq=B(A(_bA,[_6f,_m3,_9a,_nZ,_mg,_ok,_]));return _9;},_or=(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);}),_os=(function(x){return document.getElementById(x).value;}),_ot=0,_ou=[0,_ot,_ot],_ov=397,_ow=[0,_ov,_ot],_ox=223,_oy=[0,_ov,_ox],_oz=[0,_ot,_ox],_oA=[0,_ou,_oz,_oy,_ow],_oB=[0,_1x,_oA],_oC=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:37:3-15"));}),_oD=[0,_65,_66,_2S,_oC,_65,_65],_oE=new T(function(){return B(_63(_oD));}),_oF=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:38:3-15"));}),_oG=[0,_65,_66,_2S,_oF,_65,_65],_oH=new T(function(){return B(_63(_oG));}),_oI=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:47:3-10"));}),_oJ=[0,_65,_66,_2S,_oI,_65,_65],_oK=new T(function(){return B(_63(_oJ));}),_oL=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:48:3-11"));}),_oM=[0,_65,_66,_2S,_oL,_65,_65],_oN=new T(function(){return B(_63(_oM));}),_oO=function(_){return _9;},_oP=new T(function(){return B(unCStr("loadPath"));}),_oQ=function(_oR,_){var _oS=function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);},_oT=_oS,_oU=new T(function(){return E(_oT);}),_oV=E(_oU)("processDump",toJSStr(_oP));return new F(function(){return _oO(_);});},_oW=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:65:5-17"));}),_oX=[0,_65,_66,_2S,_oW,_65,_65],_oY=new T(function(){return B(_63(_oX));}),_oZ=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:68:5-19"));}),_p0=[0,_65,_66,_2S,_oZ,_65,_65],_p1=new T(function(){return B(_63(_p0));}),_p2=new T(function(){return B(unCStr("download"));}),_p3=new T(function(){return B(unCStr(".txt"));}),_p4=new T(function(){return B(unCStr(".json"));}),_p5=new T(function(){return B(unCStr("filePath"));}),_p6=new T(function(){return B(unCStr("IndianRoller2.jpg"));}),_p7=[0,_2n,_2S],_p8=function(_){var _p9=jsFind("filePath");if(!_p9[0]){return new F(function(){return die(_oE);});}else{var _pa=jsFind("loadPath");if(!_pa[0]){return new F(function(){return die(_oH);});}else{var _pb=nMV(_oB),_pc=_pb,_pd=nMV(_p7),_pe=_pd,_pf=B(A(_3,[_6e,_p6,_])),_pg=nMV(_pf),_ph=_pg,_pi=nMV(_p6),_pj=_pi,_pk=B(A(_je,[_6e,_jl,_])),_pl=E(_pk);if(!_pl[0]){return new F(function(){return die(_oK);});}else{var _pm=B(A(_je,[_6e,_jj,_])),_pn=E(_pm);if(!_pn[0]){return new F(function(){return die(_oN);});}else{var _po=_pe,_pp=_ph,_pq=function(_){return new F(function(){return _kR(_po,_pc,_pp,_);});},_pr=B(_my(_pc,_pl[1],_pq,_)),_ps=B(_nX(_po,_pn[1],_pq,_)),_pt=function(_pu,_){var _pv=String(E(_pu)),_pw=jsParseJSON(_pv);if(!_pw[0]){return _8D;}else{var _px=B(_3A(_pw[1]));if(!_px[0]){return _8D;}else{var _py=_px[1],_pz=new T(function(){return E(E(_py)[1]);}),_=wMV(_pc,_pz),_pA=new T(function(){return E(E(_py)[2]);}),_=wMV(_pe,_pA);return _8D;}}},_pB=__createJSFunc(2,E(_pt)),_pC=(function(s,f){Haste[s] = f;}),_pD=_pC,_pE=new T(function(){return E(_pD);}),_pF=E(_pE)("processDump",_pB),_pG=function(_pH,_){var _pI=E(_pH),_pJ=toJSStr(_p5),_pK=E(_or)(_pJ),_pL=_pK,_pM=new T(function(){var _pN=String(_pL);return fromJSStr(_pN);}),_pO=B(A(_3,[_6e,_pM,_])),_=wMV(_ph,_pO),_pP=E(_os)(_pJ),_pQ=_pP,_pR=new T(function(){var _pS=String(_pQ);return fromJSStr(_pS);}),_=wMV(_pj,_pR),_pT=jsFind(toJSStr(E(_jA)));if(!_pT[0]){return new F(function(){return die(_oY);});}else{var _pU=new T(function(){return B(_G(_pR,_p4));}),_pV=B(A(_fr,[_s,_6e,_pT[1],_p2,_pU,_])),_pW=jsFind(toJSStr(E(_jB)));if(!_pW[0]){return new F(function(){return die(_p1);});}else{var _pX=new T(function(){return B(_G(_pR,_p3));}),_pY=B(A(_fr,[_s,_6e,_pW[1],_p2,_pX,_]));return new F(function(){return _kR(_po,_pc,_pp,_);});}}},_pZ=B(A(_bA,[_6f,_s,_n,_p9[1],_aW,_pG,_])),_q0=B(A(_bA,[_6f,_s,_n,_pa[1],_aW,_oQ,_]));return new F(function(){return _kR(_po,_pc,_pp,_);});}}}}},_q1=function(_){return new F(function(){return _p8(_);});};
var hasteMain = function() {B(A(_q1, [0]));};window.onload = hasteMain;