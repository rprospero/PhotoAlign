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

var _0="src",_1=function(_2){return E(E(_2)[2]);},_3=function(_4,_5){var _6=function(_){var _7=jsCreateElem("img"),_8=jsSet(_7,E(_0),toJSStr(E(_5)));return _7;};return new F(function(){return A(_1,[_4,_6]);});},_9=0,_a=function(_){return _9;},_b=function(_c,_d,_){return new F(function(){return _a(_);});},_e="scroll",_f="submit",_g="blur",_h="focus",_i="change",_j="unload",_k="load",_l=function(_m){switch(E(_m)){case 0:return E(_k);case 1:return E(_j);case 2:return E(_i);case 3:return E(_h);case 4:return E(_g);case 5:return E(_f);default:return E(_e);}},_n=[0,_l,_b],_o=function(_p,_){return [1,_p];},_q=function(_r){return E(_r);},_s=[0,_q,_o],_t=function(_u){return E(E(_u)[1]);},_v=function(_w,_x){return (!B(A(_t,[_y,_w,_x])))?true:false;},_z=function(_A,_B){var _C=strEq(E(_A),E(_B));return (E(_C)==0)?false:true;},_D=function(_E,_F){return new F(function(){return _z(_E,_F);});},_y=new T(function(){return [0,_D,_v];}),_G=function(_H,_I){var _J=E(_H);if(!_J[0]){return E(_I);}else{var _K=_J[2],_L=new T(function(){return B(_G(_K,_I));});return [1,_J[1],_L];}},_M=new T(function(){return B(unCStr("!!: negative index"));}),_N=new T(function(){return B(unCStr("Prelude."));}),_O=new T(function(){return B(_G(_N,_M));}),_P=new T(function(){return B(err(_O));}),_Q=new T(function(){return B(unCStr("!!: index too large"));}),_R=new T(function(){return B(_G(_N,_Q));}),_S=new T(function(){return B(err(_R));}),_T=function(_U,_V){while(1){var _W=E(_U);if(!_W[0]){return E(_S);}else{var _X=E(_V);if(!_X){return E(_W[1]);}else{_U=_W[2];_V=_X-1|0;continue;}}}},_Y=function(_Z,_10){if(_10>=0){return new F(function(){return _T(_Z,_10);});}else{return E(_P);}},_11=function(_12){var _13=E(_12);if(_13[0]==3){var _14=_13[1],_15=B(_Y(_14,0));if(!_15[0]){var _16=B(_Y(_14,1));return (_16[0]==0)?[1,[0,_15[1],_16[1]]]:[0];}else{return [0];}}else{return [0];}},_17=function(_18,_19){var _1a=E(_19);if(!_1a[0]){return [0];}else{var _1b=_1a[1],_1c=_1a[2],_1d=new T(function(){return B(_17(_18,_1c));}),_1e=new T(function(){return B(A(_18,[_1b]));});return [1,_1e,_1d];}},_1f=function(_1g){var _1h=E(_1g);if(_1h[0]==3){var _1i=B(_17(_11,_1h[1])),_1j=B(_Y(_1i,0));if(!_1j[0]){return [0];}else{var _1k=B(_Y(_1i,1));if(!_1k[0]){return [0];}else{var _1l=B(_Y(_1i,2));if(!_1l[0]){return [0];}else{var _1m=B(_Y(_1i,3));return (_1m[0]==0)?[0]:[1,[0,_1j[1],_1k[1],_1l[1],_1m[1]]];}}}}else{return [0];}},_1n="box",_1o="mouse",_1p="corner",_1q="Dragging",_1r=[0],_1s=[1,_1r],_1t="Free",_1u="state",_1v=1,_1w=[1,_1v],_1x=0,_1y=[1,_1x],_1z=3,_1A=[1,_1z],_1B=2,_1C=[1,_1B],_1D=new T(function(){return B(unCStr("SW"));}),_1E=new T(function(){return B(unCStr("SE"));}),_1F=new T(function(){return B(unCStr("NW"));}),_1G=new T(function(){return B(unCStr("NE"));}),_1H=function(_1I,_1J){while(1){var _1K=E(_1I);if(!_1K[0]){return (E(_1J)[0]==0)?true:false;}else{var _1L=E(_1J);if(!_1L[0]){return false;}else{if(E(_1K[1])!=E(_1L[1])){return false;}else{_1I=_1K[2];_1J=_1L[2];continue;}}}}},_1M=function(_1N){var _1O=E(_1N);if(_1O[0]==1){var _1P=fromJSStr(_1O[1]);return (!B(_1H(_1P,_1G)))?(!B(_1H(_1P,_1F)))?(!B(_1H(_1P,_1E)))?(!B(_1H(_1P,_1D)))?[0]:E(_1C):E(_1A):E(_1y):E(_1w);}else{return [0];}},_1Q=function(_1R,_1S,_1T){while(1){var _1U=E(_1T);if(!_1U[0]){return [0];}else{var _1V=E(_1U[1]);if(!B(A(_t,[_1R,_1S,_1V[1]]))){_1T=_1U[2];continue;}else{return [1,_1V[2]];}}}},_1W=function(_1X){var _1Y=E(_1X);if(_1Y[0]==4){var _1Z=_1Y[1],_20=B(_1Q(_y,_1u,_1Z));if(!_20[0]){return [0];}else{var _21=E(_20[1]);if(_21[0]==1){var _22=_21[1],_23=strEq(_22,E(_1t));if(!E(_23)){var _24=strEq(_22,E(_1q));if(!E(_24)){return [0];}else{var _25=B(_1Q(_y,_1p,_1Z));if(!_25[0]){return [0];}else{var _26=B(_1M(_25[1]));return (_26[0]==0)?[0]:[1,[1,_26[1]]];}}}else{return E(_1s);}}else{return [0];}}}else{return [0];}},_27=function(_28){var _29=E(_28);if(_29[0]==4){var _2a=_29[1],_2b=B(_1Q(_y,_1o,_2a));if(!_2b[0]){return [0];}else{var _2c=B(_1W(_2b[1]));if(!_2c[0]){return [0];}else{var _2d=B(_1Q(_y,_1n,_2a));if(!_2d[0]){return [0];}else{var _2e=B(_1f(_2d[1]));return (_2e[0]==0)?[0]:[1,[0,_2c[1],_2e[1]]];}}}}else{return [0];}},_2f=1,_2g=[1,_2f],_2h=0,_2i=[1,_2h],_2j=new T(function(){return B(unCStr("Free"));}),_2k=new T(function(){return B(unCStr("Dragging"));}),_2l=function(_2m){var _2n=E(_2m);if(_2n[0]==1){var _2o=fromJSStr(_2n[1]);return (!B(_1H(_2o,_2k)))?(!B(_1H(_2o,_2j)))?[0]:E(_2i):E(_2g);}else{return [0];}},_2p="scans",_2q="mouse",_2r=function(_2s){var _2t=E(_2s);if(_2t[0]==3){var _2u=_2t[1],_2v=B(_Y(_2u,0));if(_2v[0]==3){var _2w=_2v[1],_2x=B(_Y(_2w,0));if(!_2x[0]){var _2y=B(_Y(_2w,1));if(!_2y[0]){var _2z=B(_Y(_2u,1));if(_2z[0]==3){var _2A=_2z[1],_2B=B(_Y(_2A,0));if(!_2B[0]){var _2C=B(_Y(_2A,1));return (_2C[0]==0)?[1,[0,[0,_2x[1],_2y[1]],[0,_2B[1],_2C[1]]]]:[0];}else{return [0];}}else{return [0];}}else{return [0];}}else{return [0];}}else{return [0];}}else{return [0];}},_2D=[0],_2E=[1,_2D],_2F=function(_2G){var _2H=E(_2G);if(!_2H[0]){return E(_2E);}else{var _2I=E(_2H[1]);if(!_2I[0]){return [0];}else{var _2J=B(_2F(_2H[2]));return (_2J[0]==0)?[0]:[1,[1,_2I[1],_2J[1]]];}}},_2K=function(_2L){var _2M=E(_2L);if(_2M[0]==4){var _2N=_2M[1],_2O=B(_1Q(_y,_2q,_2N));if(!_2O[0]){return [0];}else{var _2P=B(_2l(_2O[1]));if(!_2P[0]){return [0];}else{var _2Q=B(_1Q(_y,_2p,_2N));if(!_2Q[0]){return [0];}else{var _2R=E(_2Q[1]);if(_2R[0]==3){var _2S=B(_2F(B(_17(_2r,_2R[1]))));return (_2S[0]==0)?[0]:[1,[0,_2P[1],_2S[1]]];}else{return [0];}}}}}else{return [0];}},_2T="scans",_2U="calib",_2V=function(_2W){var _2X=E(_2W);if(_2X[0]==4){var _2Y=_2X[1],_2Z=B(_1Q(_y,_2U,_2Y));if(!_2Z[0]){return [0];}else{var _30=B(_27(_2Z[1]));if(!_30[0]){return [0];}else{var _31=B(_1Q(_y,_2T,_2Y));if(!_31[0]){return [0];}else{var _32=B(_2K(_31[1]));return (_32[0]==0)?[0]:[1,[0,_30[1],_32[1]]];}}}}else{return [0];}},_33=function(_34,_35,_){var _36=B(A(_34,[_])),_37=B(A(_35,[_]));return _36;},_38=function(_39,_3a,_){var _3b=B(A(_39,[_])),_3c=_3b,_3d=B(A(_3a,[_])),_3e=_3d;return new T(function(){return B(A(_3c,[_3e]));});},_3f=function(_3g,_3h,_){var _3i=B(A(_3h,[_]));return _3g;},_3j=function(_3k,_3l,_){var _3m=B(A(_3l,[_])),_3n=_3m;return new T(function(){return B(A(_3k,[_3n]));});},_3o=[0,_3j,_3f],_3p=function(_3q,_){return _3q;},_3r=function(_3s,_3t,_){var _3u=B(A(_3s,[_]));return new F(function(){return A(_3t,[_]);});},_3v=[0,_3o,_3p,_38,_3r,_33],_3w=function(_3x,_3y,_){var _3z=B(A(_3x,[_]));return new F(function(){return A(_3y,[_3z,_]);});},_3A=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_3B=new T(function(){return B(unCStr("base"));}),_3C=new T(function(){return B(unCStr("IOException"));}),_3D=new T(function(){var _3E=hs_wordToWord64(4053623282),_3F=hs_wordToWord64(3693590983);return [0,_3E,_3F,[0,_3E,_3F,_3B,_3A,_3C],_2D,_2D];}),_3G=function(_3H){return E(_3D);},_3I=function(_3J){return E(E(_3J)[1]);},_3K=function(_3L,_3M,_3N){var _3O=B(A(_3L,[_])),_3P=B(A(_3M,[_])),_3Q=hs_eqWord64(_3O[1],_3P[1]);if(!_3Q){return [0];}else{var _3R=hs_eqWord64(_3O[2],_3P[2]);return (!_3R)?[0]:[1,_3N];}},_3S=function(_3T){var _3U=E(_3T);return new F(function(){return _3K(B(_3I(_3U[1])),_3G,_3U[2]);});},_3V=new T(function(){return B(unCStr(": "));}),_3W=new T(function(){return B(unCStr(")"));}),_3X=new T(function(){return B(unCStr(" ("));}),_3Y=new T(function(){return B(unCStr("interrupted"));}),_3Z=new T(function(){return B(unCStr("system error"));}),_40=new T(function(){return B(unCStr("unsatisified constraints"));}),_41=new T(function(){return B(unCStr("user error"));}),_42=new T(function(){return B(unCStr("permission denied"));}),_43=new T(function(){return B(unCStr("illegal operation"));}),_44=new T(function(){return B(unCStr("end of file"));}),_45=new T(function(){return B(unCStr("resource exhausted"));}),_46=new T(function(){return B(unCStr("resource busy"));}),_47=new T(function(){return B(unCStr("does not exist"));}),_48=new T(function(){return B(unCStr("already exists"));}),_49=new T(function(){return B(unCStr("resource vanished"));}),_4a=new T(function(){return B(unCStr("timeout"));}),_4b=new T(function(){return B(unCStr("unsupported operation"));}),_4c=new T(function(){return B(unCStr("hardware fault"));}),_4d=new T(function(){return B(unCStr("inappropriate type"));}),_4e=new T(function(){return B(unCStr("invalid argument"));}),_4f=new T(function(){return B(unCStr("failed"));}),_4g=new T(function(){return B(unCStr("protocol error"));}),_4h=function(_4i,_4j){switch(E(_4i)){case 0:return new F(function(){return _G(_48,_4j);});break;case 1:return new F(function(){return _G(_47,_4j);});break;case 2:return new F(function(){return _G(_46,_4j);});break;case 3:return new F(function(){return _G(_45,_4j);});break;case 4:return new F(function(){return _G(_44,_4j);});break;case 5:return new F(function(){return _G(_43,_4j);});break;case 6:return new F(function(){return _G(_42,_4j);});break;case 7:return new F(function(){return _G(_41,_4j);});break;case 8:return new F(function(){return _G(_40,_4j);});break;case 9:return new F(function(){return _G(_3Z,_4j);});break;case 10:return new F(function(){return _G(_4g,_4j);});break;case 11:return new F(function(){return _G(_4f,_4j);});break;case 12:return new F(function(){return _G(_4e,_4j);});break;case 13:return new F(function(){return _G(_4d,_4j);});break;case 14:return new F(function(){return _G(_4c,_4j);});break;case 15:return new F(function(){return _G(_4b,_4j);});break;case 16:return new F(function(){return _G(_4a,_4j);});break;case 17:return new F(function(){return _G(_49,_4j);});break;default:return new F(function(){return _G(_3Y,_4j);});}},_4k=new T(function(){return B(unCStr("}"));}),_4l=new T(function(){return B(unCStr("{handle: "));}),_4m=function(_4n,_4o,_4p,_4q,_4r,_4s){var _4t=new T(function(){var _4u=new T(function(){var _4v=new T(function(){var _4w=E(_4q);if(!_4w[0]){return E(_4s);}else{var _4x=new T(function(){var _4y=new T(function(){return B(_G(_3W,_4s));},1);return B(_G(_4w,_4y));},1);return B(_G(_3X,_4x));}},1);return B(_4h(_4o,_4v));}),_4z=E(_4p);if(!_4z[0]){return E(_4u);}else{var _4A=new T(function(){return B(_G(_3V,_4u));},1);return B(_G(_4z,_4A));}}),_4B=E(_4r);if(!_4B[0]){var _4C=E(_4n);if(!_4C[0]){return E(_4t);}else{var _4D=E(_4C[1]);if(!_4D[0]){var _4E=_4D[1],_4F=new T(function(){var _4G=new T(function(){var _4H=new T(function(){return B(_G(_3V,_4t));},1);return B(_G(_4k,_4H));},1);return B(_G(_4E,_4G));},1);return new F(function(){return _G(_4l,_4F);});}else{var _4I=_4D[1],_4J=new T(function(){var _4K=new T(function(){var _4L=new T(function(){return B(_G(_3V,_4t));},1);return B(_G(_4k,_4L));},1);return B(_G(_4I,_4K));},1);return new F(function(){return _G(_4l,_4J);});}}}else{var _4M=new T(function(){return B(_G(_3V,_4t));},1);return new F(function(){return _G(_4B[1],_4M);});}},_4N=function(_4O){var _4P=E(_4O);return new F(function(){return _4m(_4P[1],_4P[2],_4P[3],_4P[4],_4P[6],_2D);});},_4Q=function(_4R,_4S,_4T){var _4U=E(_4S);return new F(function(){return _4m(_4U[1],_4U[2],_4U[3],_4U[4],_4U[6],_4T);});},_4V=function(_4W,_4X){var _4Y=E(_4W);return new F(function(){return _4m(_4Y[1],_4Y[2],_4Y[3],_4Y[4],_4Y[6],_4X);});},_4Z=44,_50=93,_51=91,_52=function(_53,_54,_55){var _56=E(_54);if(!_56[0]){return new F(function(){return unAppCStr("[]",_55);});}else{var _57=_56[1],_58=_56[2],_59=new T(function(){var _5a=new T(function(){var _5b=[1,_50,_55],_5c=function(_5d){var _5e=E(_5d);if(!_5e[0]){return E(_5b);}else{var _5f=_5e[1],_5g=_5e[2],_5h=new T(function(){var _5i=new T(function(){return B(_5c(_5g));});return B(A(_53,[_5f,_5i]));});return [1,_4Z,_5h];}};return B(_5c(_58));});return B(A(_53,[_57,_5a]));});return [1,_51,_59];}},_5j=function(_5k,_5l){return new F(function(){return _52(_4V,_5k,_5l);});},_5m=[0,_4Q,_4N,_5j],_5n=new T(function(){return [0,_3G,_5m,_5o,_3S,_4N];}),_5o=function(_5p){return [0,_5n,_5p];},_5q=[0],_5r=7,_5s=function(_5t){return [0,_5q,_5r,_2D,_5t,_5q,_5q];},_5u=function(_5v,_){var _5w=new T(function(){var _5x=new T(function(){return B(_5s(_5v));});return B(_5o(_5x));});return new F(function(){return die(_5w);});},_5y=[0,_3v,_3w,_3r,_3p,_5u],_5z=[0,_5y,_q],_5A=[0,_5z,_3p],_5B=function(_5C,_5D){return E(_5C)==E(_5D);},_5E=function(_5F,_5G,_5H,_5I,_5J,_5K){if(_5F!=_5I){return false;}else{if(E(_5G)!=E(_5J)){return false;}else{var _5L=E(_5H),_5M=E(_5K);if(E(_5L[1])!=E(_5M[1])){return false;}else{return new F(function(){return _5B(_5L[2],_5M[2]);});}}}},_5N=function(_5O,_5P){var _5Q=E(_5O),_5R=E(_5Q[1]),_5S=E(_5P),_5T=E(_5S[1]);return new F(function(){return _5E(E(_5R[1]),_5R[2],_5Q[2],E(_5T[1]),_5T[2],_5S[2]);});},_5U="scans",_5V=[1,_5U,_2D],_5W="calib",_5X=[1,_5W,_5V],_5Y=function(_5Z){return [0,E(_5Z)];},_60=function(_61){var _62=E(_61),_63=_62[1],_64=_62[2],_65=new T(function(){return B(_5Y(_64));}),_66=new T(function(){return B(_5Y(_63));});return [3,[1,_66,[1,_65,_2D]]];},_67=new T(function(){return [1,"Dragging"];}),_68=[0,_1u,_67],_69=new T(function(){return [1,"Free"];}),_6a="state",_6b=[0,_6a,_69],_6c=[1,_6b,_2D],_6d=[4,E(_6c)],_6e=function(_6f,_6g){switch(E(_6f)){case 0:return new F(function(){return _G(_1F,_6g);});break;case 1:return new F(function(){return _G(_1G,_6g);});break;case 2:return new F(function(){return _G(_1D,_6g);});break;default:return new F(function(){return _G(_1E,_6g);});}},_6h=function(_6i){return E(toJSStr(B(_6e(_6i,_2D))));},_6j=function(_6k){return [1,B(_6h(_6k))];},_6l=function(_6m){var _6n=new T(function(){var _6o=E(E(_6m)[2]),_6p=_6o[1],_6q=_6o[2],_6r=_6o[3],_6s=_6o[4],_6t=new T(function(){return B(_60(_6s));}),_6u=new T(function(){return B(_60(_6r));}),_6v=new T(function(){return B(_60(_6q));}),_6w=new T(function(){return B(_60(_6p));});return [3,[1,_6w,[1,_6v,[1,_6u,[1,_6t,_2D]]]]];}),_6x=new T(function(){var _6y=E(E(_6m)[1]);if(!_6y[0]){return E(_6d);}else{var _6z=_6y[1],_6A=new T(function(){return B(_6j(_6z));});return [4,[1,_68,[1,[0,_1p,_6A],_2D]]];}});return [1,[0,_1o,_6x],[1,[0,_1n,_6n],_2D]];},_6B="scans",_6C=[1,_6B,_2D],_6D="mouse",_6E=[1,_6D,_6C],_6F=function(_6G){var _6H=new T(function(){var _6I=E(E(_6G)[2]),_6J=_6I[1],_6K=_6I[2],_6L=new T(function(){return B(_5Y(_6K));}),_6M=new T(function(){return B(_5Y(_6J));});return [3,[1,_6M,[1,_6L,_2D]]];}),_6N=new T(function(){var _6O=E(E(_6G)[1]),_6P=_6O[1],_6Q=_6O[2],_6R=new T(function(){return B(_5Y(_6Q));}),_6S=new T(function(){return B(_5Y(_6P));});return [3,[1,_6S,[1,_6R,_2D]]];});return [1,_6N,[1,_6H,_2D]];},_6T=function(_6U){return [3,E(B(_6F(_6U)))];},_6V=function(_6W,_6X){var _6Y=E(_6W);if(!_6Y[0]){return [0];}else{var _6Z=_6Y[2],_70=E(_6X);if(!_70[0]){return [0];}else{var _71=_70[2],_72=new T(function(){return B(_6V(_6Z,_71));});return [1,[0,_6Y[1],_70[1]],_72];}}},_73=function(_74){var _75=new T(function(){return [3,E(B(_17(_6T,E(_74)[2])))];}),_76=new T(function(){if(!E(E(_74)[1])){return [1,toJSStr(E(_2j))];}else{return [1,toJSStr(E(_2k))];}});return new F(function(){return _6V(_6E,[1,_76,[1,_75,_2D]]);});},_77=function(_78){return [1,E(_78)];},_79="deltaZ",_7a="deltaY",_7b="deltaX",_7c=function(_7d,_7e){var _7f=jsShowI(_7d);return new F(function(){return _G(fromJSStr(_7f),_7e);});},_7g=41,_7h=40,_7i=function(_7j,_7k,_7l){if(_7k>=0){return new F(function(){return _7c(_7k,_7l);});}else{if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{var _7m=new T(function(){var _7n=jsShowI(_7k);return B(_G(fromJSStr(_7n),[1,_7g,_7l]));});return [1,_7h,_7m];}}},_7o=new T(function(){return B(unCStr(")"));}),_7p=new T(function(){return B(_7i(0,2,_7o));}),_7q=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_7p));}),_7r=function(_7s){var _7t=new T(function(){return B(_7i(0,_7s,_7q));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_7t)));});},_7u=function(_7v,_){return new T(function(){var _7w=Number(E(_7v)),_7x=jsTrunc(_7w);if(_7x<0){return B(_7r(_7x));}else{if(_7x>2){return B(_7r(_7x));}else{return _7x;}}});},_7y=0,_7z=[0,_7y,_7y,_7y],_7A="button",_7B=new T(function(){return jsGetMouseCoords;}),_7C=function(_7D,_){var _7E=E(_7D);if(!_7E[0]){return _2D;}else{var _7F=_7E[1],_7G=B(_7C(_7E[2],_)),_7H=new T(function(){var _7I=Number(E(_7F));return jsTrunc(_7I);});return [1,_7H,_7G];}},_7J=function(_7K,_){var _7L=__arr2lst(0,_7K);return new F(function(){return _7C(_7L,_);});},_7M=function(_7N,_){return new F(function(){return _7J(E(_7N),_);});},_7O=function(_7P,_){return new T(function(){var _7Q=Number(E(_7P));return jsTrunc(_7Q);});},_7R=[0,_7O,_7M],_7S=function(_7T,_){var _7U=E(_7T);if(!_7U[0]){return _2D;}else{var _7V=B(_7S(_7U[2],_));return [1,_7U[1],_7V];}},_7W=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_7X=[0,_5q,_5r,_2D,_7W,_5q,_5q],_7Y=new T(function(){return B(_5o(_7X));}),_7Z=function(_){return new F(function(){return die(_7Y);});},_80=function(_81){return E(E(_81)[1]);},_82=function(_83,_84,_85,_){var _86=__arr2lst(0,_85),_87=B(_7S(_86,_)),_88=E(_87);if(!_88[0]){return new F(function(){return _7Z(_);});}else{var _89=E(_88[2]);if(!_89[0]){return new F(function(){return _7Z(_);});}else{if(!E(_89[2])[0]){var _8a=B(A(_80,[_83,_88[1],_])),_8b=B(A(_80,[_84,_89[1],_]));return [0,_8a,_8b];}else{return new F(function(){return _7Z(_);});}}}},_8c=function(_){return new F(function(){return __jsNull();});},_8d=function(_8e){var _8f=B(A(_8e,[_]));return E(_8f);},_8g=new T(function(){return B(_8d(_8c));}),_8h=new T(function(){return E(_8g);}),_8i=function(_8j,_8k,_){if(E(_8j)==7){var _8l=E(_7B)(_8k),_8m=B(_82(_7R,_7R,_8l,_)),_8n=_8m,_8o=_8k[E(_7b)],_8p=_8o,_8q=_8k[E(_7a)],_8r=_8q,_8s=_8k[E(_79)],_8t=_8s;return new T(function(){return [0,E(_8n),E(_5q),[0,_8p,_8r,_8t]];});}else{var _8u=E(_7B)(_8k),_8v=B(_82(_7R,_7R,_8u,_)),_8w=_8v,_8x=_8k[E(_7A)],_8y=__eq(_8x,E(_8h));if(!E(_8y)){var _8z=B(_7u(_8x,_)),_8A=_8z;return new T(function(){return [0,E(_8w),[1,_8A],E(_7z)];});}else{return new T(function(){return [0,E(_8w),E(_5q),E(_7z)];});}}},_8B=function(_8C,_8D,_){return new F(function(){return _8i(_8C,E(_8D),_);});},_8E="mouseout",_8F="mouseover",_8G="mousemove",_8H="mouseup",_8I="mousedown",_8J="dblclick",_8K="click",_8L="wheel",_8M=function(_8N){switch(E(_8N)){case 0:return E(_8K);case 1:return E(_8J);case 2:return E(_8I);case 3:return E(_8H);case 4:return E(_8G);case 5:return E(_8F);case 6:return E(_8E);default:return E(_8L);}},_8O=[0,_8M,_8B],_8P=function(_8Q,_){var _8R=E(_8Q);if(!_8R[0]){return _2D;}else{var _8S=B(A(_8R[1],[_])),_8T=B(_8P(_8R[2],_));return [1,_8S,_8T];}},_8U=function(_8V,_8W,_){var _8X=B(A(_8V,[_])),_8Y=B(_8P(_8W,_));return [1,_8X,_8Y];},_8Z=function(_){return new F(function(){return jsCreateElem("th");});},_90=function(_91,_92){var _93=function(_){return new F(function(){return jsCreateTextNode(toJSStr(E(_92)));});};return new F(function(){return A(_1,[_91,_93]);});},_94=function(_95){return E(E(_95)[1]);},_96=function(_97){return E(E(_97)[3]);},_98=function(_99){return E(E(_99)[2]);},_9a=function(_9b){return E(E(_9b)[4]);},_9c=function(_9d){return E(E(_9d)[1]);},_9e=function(_9f,_9g,_9h,_9i){var _9j=new T(function(){return B(A(_9c,[_9f,_9h]));}),_9k=function(_9l,_){var _9m=E(_9l);if(!_9m[0]){return _9;}else{var _9n=E(_9j),_9o=jsAppendChild(E(_9m[1]),_9n),_9p=_9m[2],_=_;while(1){var _9q=E(_9p);if(!_9q[0]){return _9;}else{var _9r=jsAppendChild(E(_9q[1]),_9n);_9p=_9q[2];continue;}}}},_9s=function(_9t,_){while(1){var _9u=(function(_9v,_){var _9w=E(_9v);if(!_9w[0]){return _9;}else{var _9x=_9w[2],_9y=E(_9w[1]);if(!_9y[0]){var _9z=_9y[2],_9A=E(_9y[1]);switch(_9A[0]){case 0:var _9B=E(_9j),_9C=jsSet(_9B,_9A[1],_9z),_9D=_9x,_=_;while(1){var _9E=E(_9D);if(!_9E[0]){return _9;}else{var _9F=_9E[2],_9G=E(_9E[1]);if(!_9G[0]){var _9H=_9G[2],_9I=E(_9G[1]);switch(_9I[0]){case 0:var _9J=jsSet(_9B,_9I[1],_9H);_9D=_9F;continue;case 1:var _9K=jsSetStyle(_9B,_9I[1],_9H);_9D=_9F;continue;default:var _9L=jsSetAttr(_9B,_9I[1],_9H);_9D=_9F;continue;}}else{var _9M=B(_9k(_9G[1],_));_9D=_9F;continue;}}}break;case 1:var _9N=E(_9j),_9O=jsSetStyle(_9N,_9A[1],_9z),_9P=_9x,_=_;while(1){var _9Q=E(_9P);if(!_9Q[0]){return _9;}else{var _9R=_9Q[2],_9S=E(_9Q[1]);if(!_9S[0]){var _9T=_9S[2],_9U=E(_9S[1]);switch(_9U[0]){case 0:var _9V=jsSet(_9N,_9U[1],_9T);_9P=_9R;continue;case 1:var _9W=jsSetStyle(_9N,_9U[1],_9T);_9P=_9R;continue;default:var _9X=jsSetAttr(_9N,_9U[1],_9T);_9P=_9R;continue;}}else{var _9Y=B(_9k(_9S[1],_));_9P=_9R;continue;}}}break;default:var _9Z=E(_9j),_a0=jsSetAttr(_9Z,_9A[1],_9z),_a1=_9x,_=_;while(1){var _a2=E(_a1);if(!_a2[0]){return _9;}else{var _a3=_a2[2],_a4=E(_a2[1]);if(!_a4[0]){var _a5=_a4[2],_a6=E(_a4[1]);switch(_a6[0]){case 0:var _a7=jsSet(_9Z,_a6[1],_a5);_a1=_a3;continue;case 1:var _a8=jsSetStyle(_9Z,_a6[1],_a5);_a1=_a3;continue;default:var _a9=jsSetAttr(_9Z,_a6[1],_a5);_a1=_a3;continue;}}else{var _aa=B(_9k(_a4[1],_));_a1=_a3;continue;}}}}}else{var _ab=B(_9k(_9y[1],_));_9t=_9x;return null;}}})(_9t,_);if(_9u!=null){return _9u;}}},_ac=function(_){return new F(function(){return _9s(_9i,_);});};return new F(function(){return A(_1,[_9g,_ac]);});},_ad=function(_ae,_af,_ag,_ah){var _ai=B(_94(_af)),_aj=function(_ak){var _al=new T(function(){return B(A(_9a,[_ai,_ak]));}),_am=new T(function(){return B(_9e(_ae,_af,_ak,_ah));});return new F(function(){return A(_96,[_ai,_am,_al]);});};return new F(function(){return A(_98,[_ai,_ag,_aj]);});},_an=function(_ao,_){var _ap=E(_ao);if(!_ap[0]){return _2D;}else{var _aq=B(A(_90,[_5z,_ap[1],_])),_ar=B(A(_ad,[_s,_5z,_8Z,[1,[1,[1,_aq,_2D]],_2D],_])),_as=B(_an(_ap[2],_));return [1,_ar,_as];}},_at=function(_au,_av,_){var _aw=B(A(_90,[_5z,_au,_])),_ax=B(A(_ad,[_s,_5z,_8Z,[1,[1,[1,_aw,_2D]],_2D],_])),_ay=B(_an(_av,_));return [1,_ax,_ay];},_az=function(_){return new F(function(){return jsCreateElem("td");});},_aA=function(_aB,_){var _aC=jsShow(_aB),_aD=jsCreateTextNode(toJSStr(fromJSStr(_aC)));return new F(function(){return A(_ad,[_s,_5z,_az,[1,[1,[1,_aD,_2D]],_2D],_]);});},_aE=0,_aF=function(_){return new F(function(){return jsCreateElem("tr");});},_aG=new T(function(){return B(unCStr("x1"));}),_aH=new T(function(){return B(unCStr("y1"));}),_aI=new T(function(){return B(unCStr("x2"));}),_aJ=new T(function(){return B(unCStr("y2"));}),_aK=new T(function(){return B(unCStr("Delete"));}),_aL=[1,_aK,_2D],_aM=[1,_aJ,_aL],_aN=[1,_aI,_aM],_aO=[1,_aH,_aN],_aP=function(_){return new F(function(){return jsCreateElem("span");});},_aQ=new T(function(){return [0,[2,"class"],"glyphicon glyphicon-remove"];}),_aR=[1,_aQ,_2D],_aS=new T(function(){return B(_ad(_s,_5z,_aP,_aR));}),_aT=function(_){return new F(function(){return jsCreateElem("button");});},_aU=function(_aV,_){var _aW=E(_aV);if(!_aW[0]){return _2D;}else{var _aX=B(A(_aW[1],[_])),_aY=B(_aU(_aW[2],_));return [1,_aX,_aY];}},_aZ=function(_b0){return new F(function(){return _ad(_s,_5z,_az,[1,[1,[1,_b0,_2D]],_2D]);});},_b1=new T(function(){return [0,[2,"class"],"btn btn-danger"];}),_b2=function(_b3){return E(E(_b3)[1]);},_b4=function(_b5){return E(E(_b5)[2]);},_b6=function(_b7){return E(E(_b7)[1]);},_b8=function(_){return new F(function(){return nMV(_5q);});},_b9=new T(function(){return B(_8d(_b8));}),_ba=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_bb=function(_bc){return E(E(_bc)[2]);},_bd=function(_be,_bf,_bg,_bh,_bi,_bj){var _bk=B(_b2(_be)),_bl=B(_94(_bk)),_bm=new T(function(){return B(_1(_bk));}),_bn=new T(function(){return B(_9a(_bl));}),_bo=new T(function(){return B(A(_9c,[_bf,_bh]));}),_bp=new T(function(){return B(A(_b6,[_bg,_bi]));}),_bq=function(_br){return new F(function(){return A(_bn,[[0,_bp,_bo,_br]]);});},_bs=function(_bt){var _bu=new T(function(){var _bv=new T(function(){var _bw=E(_bo),_bx=E(_bp),_by=E(_bt),_bz=function(_bA,_){var _bB=B(A(_by,[_bA,_]));return _8h;},_bC=__createJSFunc(2,E(_bz)),_bD=_bC,_bE=function(_){return new F(function(){return E(_ba)(_bw,_bx,_bD);});};return E(_bE);});return B(A(_bm,[_bv]));});return new F(function(){return A(_98,[_bl,_bu,_bq]);});},_bF=new T(function(){var _bG=new T(function(){return B(_1(_bk));}),_bH=function(_bI){var _bJ=new T(function(){var _bK=function(_){var _=wMV(E(_b9),[1,_bI]);return new F(function(){return A(_b4,[_bg,_bi,_bI,_]);});};return B(A(_bG,[_bK]));});return new F(function(){return A(_98,[_bl,_bJ,_bj]);});};return B(A(_bb,[_be,_bH]));});return new F(function(){return A(_98,[_bl,_bF,_bs]);});},_bL=function(_bM,_bN){while(1){var _bO=E(_bM);if(!_bO[0]){return E(_bN);}else{_bM=_bO[2];var _bP=[1,_bO[1],_bN];_bN=_bP;continue;}}},_bQ=function(_bR,_bS,_bT,_){var _bU=jsClearChildren(_bT),_bV=B(_at(_aG,_aO,_)),_bW=_bV,_bX=new T(function(){return B(_77(_bW));}),_bY=B(A(_ad,[_s,_5z,_aF,[1,_bX,_2D],_])),_bZ=jsAppendChild(E(_bY),_bT),_c0=function(_c1,_){var _c2=E(_c1);if(!_c2[0]){return _2D;}else{var _c3=E(_c2[1]),_c4=E(_c3[1]),_c5=_c4[1],_c6=_c4[2],_c7=E(_c3[2]),_c8=_c7[1],_c9=_c7[2],_ca=function(_){return new F(function(){return _aA(E(_c9)*25/400,_);});},_cb=function(_){return new F(function(){return _aA(E(_c8)*25/400,_);});},_cc=function(_){return new F(function(){return _aA(E(_c6)*25/400,_);});},_cd=function(_){return new F(function(){return _aA(E(_c5)*25/400,_);});},_ce=B(_8U(_cd,[1,_cc,[1,_cb,[1,_ca,_2D]]],_)),_cf=B(_aU(B(_17(_aZ,_ce)),_)),_cg=_cf,_ch=new T(function(){return B(_77(_cg));}),_ci=B(A(_ad,[_s,_5z,_aF,[1,_ch,_2D],_])),_cj=B(A(_aS,[_])),_ck=B(A(_ad,[_s,_5z,_aT,[1,_b1,[1,[1,[1,_cj,_2D]],_2D]],_])),_cl=E(_ck),_cm=E(_ci),_cn=jsAppendChild(_cl,_cm),_co=new T(function(){return B(A(_bR,[_c3]));}),_cp=function(_cq){return E(_co);},_cr=B(A(_bd,[_5A,_s,_8O,_cl,_aE,_cp,_])),_cs=jsAppendChild(_cm,_bT),_ct=B(_c0(_c2[2],_));return [1,_9,_ct];}},_cu=B(_c0(B(_bL(E(_bS)[2],_2D)),_));return _9;},_cv=function(_cw,_cx,_cy,_cz,_){var _cA=jsPushState(_cz),_cB=jsScale(_cz,_cw,_cx),_cC=B(A(_cy,[_cz,_])),_cD=jsPopState(_cz);return _9;},_cE=function(_cF,_cG,_){var _cH=jsBeginPath(_cG),_cI=B(A(_cF,[_cG,_])),_cJ=jsStroke(_cG);return _9;},_cK=",",_cL="[",_cM="]",_cN="{",_cO="}",_cP=":",_cQ="\"",_cR="true",_cS="false",_cT="null",_cU=function(_cV){return new F(function(){return jsStringify(E(_cV));});},_cW=function(_cX){return new F(function(){return _cU(_cX);});},_cY=function(_cZ,_d0){var _d1=E(_d0);switch(_d1[0]){case 0:var _d2=_d1[1],_d3=new T(function(){return jsShow(_d2);});return [0,_d3,_cZ];case 1:var _d4=_d1[1],_d5=new T(function(){return jsStringify(_d4);});return [0,_d5,_cZ];case 2:return (!E(_d1[1]))?[0,_cS,_cZ]:[0,_cR,_cZ];case 3:var _d6=E(_d1[1]);if(!_d6[0]){return [0,_cL,[1,_cM,_cZ]];}else{var _d7=_d6[1],_d8=_d6[2],_d9=new T(function(){var _da=new T(function(){var _db=[1,_cM,_cZ],_dc=function(_dd){var _de=E(_dd);if(!_de[0]){return E(_db);}else{var _df=_de[1],_dg=_de[2],_dh=new T(function(){var _di=new T(function(){return B(_dc(_dg));}),_dj=B(_cY(_di,_df));return [1,_dj[1],_dj[2]];});return [1,_cK,_dh];}};return B(_dc(_d8));}),_dk=B(_cY(_da,_d7));return [1,_dk[1],_dk[2]];});return [0,_cL,_d9];}break;case 4:var _dl=E(_d1[1]);if(!_dl[0]){return [0,_cN,[1,_cO,_cZ]];}else{var _dm=_dl[2],_dn=E(_dl[1]),_do=_dn[1],_dp=_dn[2],_dq=new T(function(){var _dr=new T(function(){var _ds=[1,_cO,_cZ],_dt=function(_du){var _dv=E(_du);if(!_dv[0]){return E(_ds);}else{var _dw=_dv[2],_dx=E(_dv[1]),_dy=_dx[2],_dz=new T(function(){var _dA=new T(function(){return B(_dt(_dw));}),_dB=B(_cY(_dA,_dy));return [1,_dB[1],_dB[2]];});return [1,_cK,[1,_cQ,[1,_dx[1],[1,_cQ,[1,_cP,_dz]]]]];}};return B(_dt(_dm));}),_dC=B(_cY(_dr,_dp));return [1,_dC[1],_dC[2]];}),_dD=new T(function(){return B(_cW(_do));});return [0,_cN,[1,_dD,[1,_cP,_dq]]];}break;default:return [0,_cT,_cZ];}},_dE=new T(function(){return toJSStr(_2D);}),_dF=function(_dG){var _dH=B(_cY(_2D,_dG)),_dI=jsCat([1,_dH[1],_dH[2]],E(_dE));return E(_dI);},_dJ=function(_dK){var _dL=E(_dK);if(!_dL[0]){return [0];}else{var _dM=_dL[2],_dN=new T(function(){return B(_dJ(_dM));},1);return new F(function(){return _G(_dL[1],_dN);});}},_dO=function(_dP,_dQ){var _dR=E(_dQ);if(!_dR[0]){return [0];}else{var _dS=_dR[2],_dT=new T(function(){return B(_dO(_dP,_dS));});return [1,_dP,[1,_dR[1],_dT]];}},_dU=new T(function(){return B(unCStr("	"));}),_dV=function(_dW,_dX,_dY,_dZ){var _e0=new T(function(){var _e1=new T(function(){var _e2=jsShow(E(_dZ)/400*25);return fromJSStr(_e2);}),_e3=new T(function(){var _e4=jsShow(E(_dY)/400*25);return fromJSStr(_e4);}),_e5=new T(function(){var _e6=jsShow(E(_dX)/400*25);return fromJSStr(_e6);});return B(_dO(_dU,[1,_e5,[1,_e3,[1,_e1,_2D]]]));}),_e7=new T(function(){var _e8=jsShow(E(_dW)/400*25);return fromJSStr(_e8);});return new F(function(){return _dJ([1,_e7,_e0]);});},_e9=function(_ea){var _eb=E(_ea),_ec=E(_eb[1]),_ed=E(_eb[2]);return new F(function(){return _dV(_ec[1],_ec[2],_ed[1],_ed[2]);});},_ee=new T(function(){return B(unCStr("\n"));}),_ef=function(_eg){var _eh=B(_17(_e9,B(_bL(_eg,_2D))));if(!_eh[0]){return [0];}else{var _ei=_eh[2],_ej=new T(function(){return B(_dO(_ee,_ei));});return new F(function(){return _dJ([1,_eh[1],_ej]);});}},_ek=function(_el,_em){var _en=function(_){return new F(function(){return jsFind(toJSStr(E(_em)));});};return new F(function(){return A(_1,[_el,_en]);});},_eo=new T(function(){return encodeURIComponent;}),_ep=new T(function(){return B(unCStr("href"));}),_eq=new T(function(){return B(unCStr("data:text/plain;charset=utf-8,"));}),_er=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:119:3-11"));}),_es=[0,_5q,_5r,_2D,_er,_5q,_5q],_et=new T(function(){return B(_5o(_es));}),_eu=function(_ev,_ew,_ex,_ey,_ez){var _eA=function(_){var _eB=jsSetAttr(B(A(_9c,[_ev,_ex])),toJSStr(E(_ey)),toJSStr(E(_ez)));return _9;};return new F(function(){return A(_1,[_ew,_eA]);});},_eC=function(_eD,_eE,_){var _eF=B(A(_ek,[_5z,_eD,_])),_eG=E(_eF);if(!_eG[0]){return new F(function(){return die(_et);});}else{var _eH=E(_eo)(toJSStr(_eE)),_eI=_eH,_eJ=new T(function(){var _eK=new T(function(){var _eL=String(_eI);return fromJSStr(_eL);},1);return B(_G(_eq,_eK));});return new F(function(){return A(_eu,[_s,_5z,_eG[1],_ep,_eJ,_]);});}},_eM=function(_eN,_eO,_eP,_){var _eQ=jsPushState(_eP),_eR=jsRotate(_eP,_eN),_eS=B(A(_eO,[_eP,_])),_eT=jsPopState(_eP);return _9;},_eU=function(_eV,_eW,_eX,_eY,_){var _eZ=jsPushState(_eY),_f0=jsTranslate(_eY,_eV,_eW),_f1=B(A(_eX,[_eY,_])),_f2=jsPopState(_eY);return _9;},_f3=function(_f4,_f5){if(_f5<=0){var _f6=function(_f7){var _f8=function(_f9){var _fa=function(_fb){var _fc=function(_fd){var _fe=isDoubleNegativeZero(_f5),_ff=_fe,_fg=function(_fh){var _fi=E(_f4);if(!_fi){return (_f5>=0)?(E(_ff)==0)?E(_f5):3.141592653589793:3.141592653589793;}else{var _fj=E(_f5);return (_fj==0)?E(_fi):_fj+_fi;}};if(!E(_ff)){return new F(function(){return _fg(_);});}else{var _fk=E(_f4),_fl=isDoubleNegativeZero(_fk);if(!E(_fl)){return new F(function(){return _fg(_);});}else{return  -B(_f3( -_fk,_f5));}}};if(_f5>=0){return new F(function(){return _fc(_);});}else{var _fm=E(_f4),_fn=isDoubleNegativeZero(_fm);if(!E(_fn)){return new F(function(){return _fc(_);});}else{return  -B(_f3( -_fm,_f5));}}};if(_f5>0){return new F(function(){return _fa(_);});}else{var _fo=E(_f4);if(_fo>=0){return new F(function(){return _fa(_);});}else{return  -B(_f3( -_fo,_f5));}}};if(_f5>=0){return new F(function(){return _f8(_);});}else{var _fp=E(_f4);if(_fp<=0){return new F(function(){return _f8(_);});}else{return 3.141592653589793+Math.atan(_fp/_f5);}}};if(!E(_f5)){if(E(_f4)<=0){return new F(function(){return _f6(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _f6(_);});}}else{return new F(function(){return Math.atan(E(_f4)/_f5);});}},_fq=function(_fr,_fs){return E(_fr)-E(_fs);},_ft=function(_fu,_fv,_fw,_fx,_fy,_fz,_fA,_fB){var _fC=new T(function(){return B(_fq(_fx,_fv));}),_fD=new T(function(){return B(_fq(_fz,_fx));}),_fE=new T(function(){return B(_fq(_fB,_fz));}),_fF=new T(function(){return B(_fq(_fv,_fB));});return new F(function(){return Math.atan((Math.tan(B(_f3(_fC,_fw-_fu))-1.5707963267948966)+Math.tan(B(_f3(_fD,_fy-_fw)))+Math.tan(B(_f3(_fE,_fA-_fy))+1.5707963267948966)+Math.tan(B(_f3(_fF,_fu-_fA))-3.141592653589793))/4);});},_fG=function(_fH){return E(_fH)/2;},_fI=function(_fJ,_fK,_fL,_){var _fM=E(_fJ);return new F(function(){return _eU(E(_fM[1]),E(_fM[2]),_fK,E(_fL),_);});},_fN=function(_fO,_fP){var _fQ=new T(function(){var _fR=E(_fO),_fS=E(E(_fP)[2]),_fT=E(_fS[1]),_fU=E(_fT[1]),_fV=E(_fT[2]),_fW=E(_fS[2]),_fX=E(_fW[1]),_fY=E(_fW[2]),_fZ=E(_fS[3]),_g0=E(_fZ[1]),_g1=E(_fZ[2]),_g2=E(_fS[4]),_g3=E(_g2[1]),_g4=E(_g2[2]);return Math.sqrt(E(_fR[1])*E(_fR[2])/(0.5*(_fU*_g4+_g3*_g1+_g0*_fV-_fU*_g1-_g0*_g4-_g3*_fV)+0.5*(_g3*_g1+_g0*_fY+_fX*_g4-_g3*_fY-_fX*_g1-_g0*_g4)));}),_g5=new T(function(){var _g6=E(_fO),_g7=_g6[1],_g8=_g6[2],_g9=new T(function(){return B(_fG(_g8));}),_ga=new T(function(){return B(_fG(_g7));});return [0,_ga,_g9];}),_gb=new T(function(){var _gc=E(E(_fP)[2]),_gd=E(_gc[1]),_ge=E(_gc[2]),_gf=E(_gc[3]),_gg=E(_gc[4]);return  -B(_ft(E(_gd[1]),_gd[2],E(_ge[1]),_ge[2],E(_gf[1]),_gf[2],E(_gg[1]),_gg[2]));}),_gh=new T(function(){var _gi=E(E(_fP)[2]),_gj=E(_gi[1]),_gk=_gj[1],_gl=_gj[2],_gm=E(_gi[2]),_gn=_gm[1],_go=_gm[2],_gp=E(_gi[3]),_gq=_gp[1],_gr=_gp[2],_gs=E(_gi[4]),_gt=_gs[1],_gu=_gs[2],_gv=new T(function(){return (E(_gl)+E(_go)+E(_gr)+E(_gu))/4/(-1);}),_gw=new T(function(){return (E(_gk)+E(_gn)+E(_gq)+E(_gt))/4/(-1);});return [0,_gw,_gv];}),_gx=function(_gy,_gz,_){var _gA=E(_g5),_gB=function(_gC,_){var _gD=E(_fQ),_gE=function(_gF,_){var _gG=function(_gH,_){return new F(function(){return _fI(_gh,_gy,_gH,_);});};return new F(function(){return _eM(E(_gb),_gG,E(_gF),_);});};return new F(function(){return _cv(_gD,_gD,_gE,E(_gC),_);});};return new F(function(){return _eU(E(_gA[1]),E(_gA[2]),_gB,E(_gz),_);});};return E(_gx);},_gI=function(_gJ,_gK,_){var _gL=E(_gJ);if(!_gL[0]){return _9;}else{var _gM=E(_gL[1]),_gN=E(_gK),_gO=jsMoveTo(_gN,E(_gM[1]),E(_gM[2])),_gP=_gL[2],_=_;while(1){var _gQ=E(_gP);if(!_gQ[0]){return _9;}else{var _gR=E(_gQ[1]),_gS=jsLineTo(_gN,E(_gR[1]),E(_gR[2]));_gP=_gQ[2];continue;}}}},_gT=function(_gU,_gV,_){var _gW=new T(function(){return E(E(_gU)[2]);}),_gX=new T(function(){return E(E(_gW)[1]);}),_gY=new T(function(){return E(E(_gW)[4]);}),_gZ=new T(function(){return E(E(_gW)[3]);}),_h0=new T(function(){return E(E(_gW)[2]);});return new F(function(){return _gI([1,_gX,[1,_h0,[1,_gZ,[1,_gY,[1,_gX,_2D]]]]],_gV,_);});},_h1=function(_h2,_h3,_h4){var _h5=E(_h4);if(!_h5[0]){return [0];}else{var _h6=_h5[1],_h7=_h5[2];if(!B(A(_h2,[_h3,_h6]))){var _h8=new T(function(){return B(_h1(_h2,_h3,_h7));});return [1,_h6,_h8];}else{return E(_h7);}}},_h9="lineWidth",_ha=function(_hb,_hc){var _hd=new T(function(){return String(E(_hb));}),_he=function(_hf,_){var _hg=E(_hf),_hh=E(_h9),_hi=jsGet(_hg,_hh),_hj=jsSet(_hg,_hh,E(_hd)),_hk=B(A(_hc,[_hg,_])),_hl=jsSet(_hg,_hh,_hi);return _9;};return E(_he);},_hm=1,_hn=400,_ho=[0,_hn,_hn],_hp=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:90:3-10"));}),_hq=function(_hr,_){var _hs=jsHasCtx2D(_hr);if(!E(_hs)){return _5q;}else{var _ht=jsGetCtx2D(_hr);return [1,[0,_ht,_hr]];}},_hu=function(_hv,_){return new F(function(){return _hq(E(_hv),_);});},_hw=function(_hx,_hy){var _hz=function(_){var _hA=jsFind(toJSStr(E(_hy)));if(!_hA[0]){return _5q;}else{return new F(function(){return _hu(_hA[1],_);});}};return new F(function(){return A(_1,[_hx,_hz]);});},_hB=new T(function(){return B(unCStr("aligned"));}),_hC=new T(function(){return B(_hw(_5z,_hB));}),_hD=new T(function(){return B(unCStr("original"));}),_hE=new T(function(){return B(_hw(_5z,_hD));}),_hF=new T(function(){return B(unCStr("scans"));}),_hG=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:89:3-11"));}),_hH=[0,_5q,_5r,_2D,_hG,_5q,_5q],_hI=new T(function(){return B(_5o(_hH));}),_hJ=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:88:3-11"));}),_hK=[0,_5q,_5r,_2D,_hJ,_5q,_5q],_hL=new T(function(){return B(_5o(_hK));}),_hM=new T(function(){return B(unCStr("saveLink"));}),_hN=new T(function(){return B(unCStr("exportLink"));}),_hO=function(_hP,_hQ,_){var _hR=E(_hP);if(!_hR[0]){return _2D;}else{var _hS=E(_hR[1]),_hT=B(_gI([1,_hS[1],[1,_hS[2],_2D]],_hQ,_)),_hU=B(_hO(_hR[2],_hQ,_));return [1,_hT,_hU];}},_hV=1,_hW=function(_hX){var _hY=function(_hZ,_){var _i0=B(_hO(E(_hX)[2],_hZ,_));return _9;},_i1=function(_i2,_){return new F(function(){return _cE(_hY,E(_i2),_);});};return new F(function(){return _ha(_hV,_i1);});},_i3=function(_i4,_i5,_i6,_){var _i7=rMV(_i5),_i8=_i7,_i9=E(_i4),_ia=rMV(_i9),_ib=_ia,_ic=B(A(_hE,[_])),_id=E(_ic);if(!_id[0]){return new F(function(){return die(_hL);});}else{var _ie=B(A(_hC,[_])),_if=E(_ie);if(!_if[0]){return new F(function(){return die(_hI);});}else{var _ig=E(_hF),_ih=jsFind(toJSStr(_ig));if(!_ih[0]){return new F(function(){return _5u(_hp,_);});}else{var _ii=function(_ij,_){var _ik=rMV(_i9),_il=E(_ik),_im=_il[2],_in=new T(function(){return B(_h1(_5N,_ij,_im));}),_=wMV(_i9,[0,_il[1],_in]),_io=function(_ip,_iq,_ir,_is,_){var _it=rMV(_ir),_iu=_it,_iv=rMV(_ip),_iw=_iv,_ix=B(A(_hE,[_])),_iy=E(_ix);if(!_iy[0]){return new F(function(){return die(_hL);});}else{var _iz=B(A(_hC,[_])),_iA=E(_iz);if(!_iA[0]){return new F(function(){return die(_hI);});}else{var _iB=jsFind(toJSStr(_ig));if(!_iB[0]){return new F(function(){return _5u(_hp,_);});}else{var _iC=function(_iD,_){var _iE=rMV(_ip),_iF=E(_iE),_iG=_iF[2],_iH=new T(function(){return B(_h1(_5N,_iD,_iG));}),_=wMV(_ip,[0,_iF[1],_iH]);return new F(function(){return _io(_ip,_,_ir,_is,_);});},_iI=B(_bQ(_iC,_iw,E(_iB[1]),_)),_iJ=E(_is),_iK=rMV(_iJ),_iL=_iK,_iM=E(_iA[1]),_iN=jsResetCanvas(_iM[2]),_iO=_iM[1],_iP=function(_iQ,_){var _iR=jsDrawImage(E(_iQ),E(_iL),0,0);return _9;},_iS=function(_iT,_){return new F(function(){return _cv(0.1,0.1,_iP,E(_iT),_);});},_iU=B(A(_fN,[_ho,_iu,_iS,_iO,_])),_iV=B(A(_hW,[_iw,_iO,_])),_iW=rMV(_iJ),_iX=E(_iy[1]),_iY=_iX[1],_iZ=jsResetCanvas(_iX[2]),_j0=jsPushState(_iY),_j1=jsScale(_iY,0.1,0.1),_j2=jsDrawImage(_iY,E(_iW),0,0),_j3=jsPopState(_iY),_j4=function(_j5,_){return new F(function(){return _gT(_iu,_j5,_);});},_j6=function(_j7,_){return new F(function(){return _cE(_j4,E(_j7),_);});},_j8=B(A(_ha,[_hm,_j6,_iY,_])),_j9=new T(function(){return B(_ef(E(_iw)[2]));},1),_ja=B(_eC(_hN,_j9,_)),_jb=new T(function(){var _jc=new T(function(){return [4,E(B(_73(_iw)))];}),_jd=new T(function(){return [4,E(B(_6l(_iu)))];});return fromJSStr(B(_dF([4,E(B(_6V(_5X,[1,_jd,[1,_jc,_2D]])))])));},1);return new F(function(){return _eC(_hM,_jb,_);});}}}};return new F(function(){return _io(_i9,_,_i5,_i6,_);});},_je=B(_bQ(_ii,_ib,E(_ih[1]),_)),_jf=E(_i6),_jg=rMV(_jf),_jh=_jg,_ji=E(_if[1]),_jj=jsResetCanvas(_ji[2]),_jk=_ji[1],_jl=function(_jm,_){var _jn=jsDrawImage(E(_jm),E(_jh),0,0);return _9;},_jo=function(_jp,_){return new F(function(){return _cv(0.1,0.1,_jl,E(_jp),_);});},_jq=B(A(_fN,[_ho,_i8,_jo,_jk,_])),_jr=B(A(_hW,[_ib,_jk,_])),_js=rMV(_jf),_jt=E(_id[1]),_ju=_jt[1],_jv=jsResetCanvas(_jt[2]),_jw=jsPushState(_ju),_jx=jsScale(_ju,0.1,0.1),_jy=jsDrawImage(_ju,E(_js),0,0),_jz=jsPopState(_ju),_jA=function(_j5,_){return new F(function(){return _gT(_i8,_j5,_);});},_jB=function(_jC,_){return new F(function(){return _cE(_jA,E(_jC),_);});},_jD=B(A(_ha,[_hm,_jB,_ju,_])),_jE=new T(function(){return B(_ef(E(_ib)[2]));},1),_jF=B(_eC(_hN,_jE,_)),_jG=new T(function(){var _jH=new T(function(){return [4,E(B(_73(_ib)))];}),_jI=new T(function(){return [4,E(B(_6l(_i8)))];});return fromJSStr(B(_dF([4,E(B(_6V(_5X,[1,_jI,[1,_jH,_2D]])))])));},1);return new F(function(){return _eC(_hM,_jG,_);});}}}},_jJ=2,_jK=function(_jL){return E(_jL)[2];},_jM=function(_){return _5q;},_jN=function(_jO,_){return new F(function(){return _jM(_);});},_jP=[0,_jK,_jN],_jQ=function(_jR,_jS){while(1){var _jT=E(_jR);if(!_jT[0]){return E(_jS);}else{var _jU=_jT[2],_jV=E(_jT[1]);if(_jS>_jV){_jR=_jU;_jS=_jV;continue;}else{_jR=_jU;continue;}}}},_jW=function(_jX,_jY,_jZ){var _k0=E(_jX);if(_jZ>_k0){return new F(function(){return _jQ(_jY,_k0);});}else{return new F(function(){return _jQ(_jY,_jZ);});}},_k1=2,_k2=4,_k3=3,_k4=function(_k5,_k6){var _k7=function(_k8,_k9){while(1){var _ka=(function(_kb,_kc){var _kd=E(_kb);if(!_kd[0]){return [0];}else{var _ke=_kd[2];if(!B(A(_k5,[_kd[1]]))){_k8=_ke;var _kf=_kc+1|0;_k9=_kf;return null;}else{var _kg=new T(function(){return B(_k7(_ke,_kc+1|0));});return [1,_kc,_kg];}}})(_k8,_k9);if(_ka!=null){return _ka;}}},_kh=B(_k7(_k6,0));return (_kh[0]==0)?[0]:[1,_kh[1]];},_ki=function(_kj){return E(_kj);},_kk=function(_kl,_km,_kn,_){var _ko=function(_kp,_){var _kq=E(_kl),_kr=rMV(_kq),_ks=E(E(_kr)[2]),_kt=_ks[1],_ku=_ks[2],_kv=_ks[3],_kw=_ks[4],_kx=new T(function(){var _ky=new T(function(){var _kz=E(E(_kp)[1]),_kA=_kz[1],_kB=_kz[2],_kC=new T(function(){return B(_ki(_kB));}),_kD=new T(function(){return B(_ki(_kA));});return [0,_kD,_kC];}),_kE=new T(function(){var _kF=E(_ky),_kG=E(_kt);return Math.pow(E(_kF[1])-E(_kG[1]),2)+Math.pow(E(_kF[2])-E(_kG[2]),2);}),_kH=new T(function(){var _kI=E(_ky),_kJ=E(_ku);return Math.pow(E(_kI[1])-E(_kJ[1]),2)+Math.pow(E(_kI[2])-E(_kJ[2]),2);}),_kK=new T(function(){var _kL=E(_ky),_kM=E(_kv);return Math.pow(E(_kL[1])-E(_kM[1]),2)+Math.pow(E(_kL[2])-E(_kM[2]),2);}),_kN=new T(function(){var _kO=E(_ky),_kP=E(_kw);return Math.pow(E(_kO[1])-E(_kP[1]),2)+Math.pow(E(_kO[2])-E(_kP[2]),2);}),_kQ=[1,_kK,[1,_kN,_2D]],_kR=new T(function(){return B(_jW(_kH,_kQ,E(_kE)));}),_kS=function(_kT){return E(_kR)==E(_kT);},_kU=B(_k4(_kS,[1,_kE,[1,_kH,_kQ]]));if(!_kU[0]){return 3;}else{switch(E(_kU[1])){case 0:return 0;break;case 1:return 2;break;case 3:return 1;break;default:return 3;}}}),_=wMV(_kq,[0,[1,_kx],_ks]);return new F(function(){return A(_kn,[_]);});},_kV=B(A(_bd,[_5A,_jP,_8O,_km,_k1,_ko,_])),_kW=function(_kX,_){var _kY=E(_kl),_kZ=rMV(_kY),_=wMV(_kY,[0,_1r,E(_kZ)[2]]);return new F(function(){return A(_kn,[_]);});},_l0=B(A(_bd,[_5A,_jP,_8O,_km,_k3,_kW,_])),_l1=function(_l2,_){var _l3=E(_kl),_l4=rMV(_l3),_l5=E(_l4),_l6=_l5[2],_l7=E(_l5[1]);if(!_l7[0]){var _l8=E(_l5);}else{var _l9=new T(function(){var _la=E(E(_l2)[1]),_lb=_la[1],_lc=_la[2],_ld=new T(function(){return B(_ki(_lc));}),_le=new T(function(){return B(_ki(_lb));});return [0,_le,_ld];});switch(E(_l7[1])){case 0:var _lf=E(_l6),_lg=[0,_l7,[0,_l9,_lf[2],_lf[3],_lf[4]]];break;case 1:var _lh=E(_l6),_lg=[0,_l7,[0,_lh[1],_lh[2],_lh[3],_l9]];break;case 2:var _li=E(_l6),_lg=[0,_l7,[0,_li[1],_l9,_li[3],_li[4]]];break;default:var _lj=E(_l6),_lg=[0,_l7,[0,_lj[1],_lj[2],_l9,_lj[4]]];}var _l8=_lg;}var _=wMV(_l3,_l8);return new F(function(){return A(_kn,[_]);});},_lk=B(A(_bd,[_5A,_jP,_8O,_km,_k2,_l1,_]));return _9;},_ll=function(_lm,_ln,_lo){if(!E(_ln)){return [0,_2h,_lo];}else{var _lp=E(_lo);if(!_lp[0]){return [0,_2f,_2D];}else{var _lq=_lp[1],_lr=new T(function(){return E(E(_lq)[1]);}),_ls=new T(function(){var _lt=E(_lr),_lu=_lt[1],_lv=E(E(_lm)[1]),_lw=_lv[1],_lx=E(_lt[2]),_ly=E(_lv[2]),_lz=_ly-_lx;if(!_lz){var _lA=E(_lu),_lB=E(_lw),_lC=_lB-_lA;if(!_lC){return [0,_lB,_lx];}else{if(_lC<=0){if(0<= -_lC){return [0,_lB,_lx];}else{return [0,_lA,_ly];}}else{if(0<=_lC){return [0,_lB,_lx];}else{return [0,_lA,_ly];}}}}else{if(_lz<=0){var _lD=E(_lu),_lE=E(_lw),_lF=_lE-_lD;if(!_lF){if( -_lz<=0){return [0,_lE,_lx];}else{return [0,_lD,_ly];}}else{if(_lF<=0){if( -_lz<= -_lF){return [0,_lE,_lx];}else{return [0,_lD,_ly];}}else{if( -_lz<=_lF){return [0,_lE,_lx];}else{return [0,_lD,_ly];}}}}else{var _lG=E(_lu),_lH=E(_lw),_lI=_lH-_lG;if(!_lI){return [0,_lG,_ly];}else{if(_lI<=0){if(_lz<= -_lI){return [0,_lH,_lx];}else{return [0,_lG,_ly];}}else{if(_lz<=_lI){return [0,_lH,_lx];}else{return [0,_lG,_ly];}}}}}});return [0,_2f,[1,[0,_lr,_ls],_lp[2]]];}}},_lJ=function(_lK,_lL,_lM,_){var _lN=function(_lO,_){var _lP=E(_lK),_lQ=rMV(_lP),_lR=_lQ,_lS=new T(function(){var _lT=E(E(_lO)[1]),_lU=_lT[1],_lV=_lT[2],_lW=new T(function(){return B(_ki(_lV));}),_lX=new T(function(){return B(_ki(_lU));});return [0,_lX,_lW];}),_lY=new T(function(){return E(E(_lR)[2]);}),_=wMV(_lP,[0,_2f,[1,[0,_lS,_lS],_lY]]);return new F(function(){return A(_lM,[_]);});},_lZ=B(A(_bd,[_5A,_jP,_8O,_lL,_k1,_lN,_])),_m0=function(_m1,_){var _m2=E(_lK),_m3=rMV(_m2),_m4=E(_m3),_=wMV(_m2,[0,_2h,B(_ll(_m1,_m4[1],_m4[2]))[2]]);return new F(function(){return A(_lM,[_]);});},_m5=B(A(_bd,[_5A,_jP,_8O,_lL,_k3,_m0,_])),_m6=function(_m7,_){var _m8=E(_lK),_m9=rMV(_m8),_ma=E(_m9),_mb=B(_ll(_m7,_ma[1],_ma[2])),_=wMV(_m8,[0,_mb[1],_mb[2]]);return new F(function(){return A(_lM,[_]);});},_mc=B(A(_bd,[_5A,_jP,_8O,_lL,_k2,_m6,_]));return _9;},_md=(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);}),_me=(function(x){return document.getElementById(x).value;}),_mf=new T(function(){return B(unCStr("\n"));}),_mg=function(_mh,_mi,_){var _mj=jsWriteHandle(E(_mh),toJSStr(E(_mi)));return _9;},_mk=function(_ml,_mm,_){var _mn=E(_ml),_mo=jsWriteHandle(_mn,toJSStr(E(_mm)));return new F(function(){return _mg(_mn,_mf,_);});},_mp=0,_mq=[0,_mp,_mp],_mr=397,_ms=[0,_mr,_mp],_mt=223,_mu=[0,_mr,_mt],_mv=[0,_mp,_mt],_mw=[0,_mq,_mv,_mu,_ms],_mx=[0,_1r,_mw],_my=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:38:3-15"));}),_mz=[0,_5q,_5r,_2D,_my,_5q,_5q],_mA=new T(function(){return B(_5o(_mz));}),_mB=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:39:3-15"));}),_mC=[0,_5q,_5r,_2D,_mB,_5q,_5q],_mD=new T(function(){return B(_5o(_mC));}),_mE=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:48:3-10"));}),_mF=[0,_5q,_5r,_2D,_mE,_5q,_5q],_mG=new T(function(){return B(_5o(_mF));}),_mH=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:49:3-11"));}),_mI=[0,_5q,_5r,_2D,_mH,_5q,_5q],_mJ=new T(function(){return B(_5o(_mI));}),_mK=function(_){return _9;},_mL=new T(function(){return B(unCStr("loadPath"));}),_mM=function(_mN,_){var _mO=function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);},_mP=_mO,_mQ=new T(function(){return E(_mP);}),_mR=E(_mQ)("processDump",toJSStr(_mL));return new F(function(){return _mK(_);});},_mS=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:66:5-17"));}),_mT=[0,_5q,_5r,_2D,_mS,_5q,_5q],_mU=new T(function(){return B(_5o(_mT));}),_mV=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:69:5-19"));}),_mW=[0,_5q,_5r,_2D,_mV,_5q,_5q],_mX=new T(function(){return B(_5o(_mW));}),_mY=new T(function(){return B(unCStr("download"));}),_mZ=new T(function(){return B(unCStr(".txt"));}),_n0=new T(function(){return B(unCStr(".json"));}),_n1=new T(function(){return B(unCStr("filePath"));}),_n2=new T(function(){return B(unCStr("Undecoded"));}),_n3=34,_n4=[1,_n3,_2D],_n5=new T(function(){return B(unCStr("ACK"));}),_n6=new T(function(){return B(unCStr("BEL"));}),_n7=new T(function(){return B(unCStr("BS"));}),_n8=new T(function(){return B(unCStr("SP"));}),_n9=[1,_n8,_2D],_na=new T(function(){return B(unCStr("US"));}),_nb=[1,_na,_n9],_nc=new T(function(){return B(unCStr("RS"));}),_nd=[1,_nc,_nb],_ne=new T(function(){return B(unCStr("GS"));}),_nf=[1,_ne,_nd],_ng=new T(function(){return B(unCStr("FS"));}),_nh=[1,_ng,_nf],_ni=new T(function(){return B(unCStr("ESC"));}),_nj=[1,_ni,_nh],_nk=new T(function(){return B(unCStr("SUB"));}),_nl=[1,_nk,_nj],_nm=new T(function(){return B(unCStr("EM"));}),_nn=[1,_nm,_nl],_no=new T(function(){return B(unCStr("CAN"));}),_np=[1,_no,_nn],_nq=new T(function(){return B(unCStr("ETB"));}),_nr=[1,_nq,_np],_ns=new T(function(){return B(unCStr("SYN"));}),_nt=[1,_ns,_nr],_nu=new T(function(){return B(unCStr("NAK"));}),_nv=[1,_nu,_nt],_nw=new T(function(){return B(unCStr("DC4"));}),_nx=[1,_nw,_nv],_ny=new T(function(){return B(unCStr("DC3"));}),_nz=[1,_ny,_nx],_nA=new T(function(){return B(unCStr("DC2"));}),_nB=[1,_nA,_nz],_nC=new T(function(){return B(unCStr("DC1"));}),_nD=[1,_nC,_nB],_nE=new T(function(){return B(unCStr("DLE"));}),_nF=[1,_nE,_nD],_nG=new T(function(){return B(unCStr("SI"));}),_nH=[1,_nG,_nF],_nI=new T(function(){return B(unCStr("SO"));}),_nJ=[1,_nI,_nH],_nK=new T(function(){return B(unCStr("CR"));}),_nL=[1,_nK,_nJ],_nM=new T(function(){return B(unCStr("FF"));}),_nN=[1,_nM,_nL],_nO=new T(function(){return B(unCStr("VT"));}),_nP=[1,_nO,_nN],_nQ=new T(function(){return B(unCStr("LF"));}),_nR=[1,_nQ,_nP],_nS=new T(function(){return B(unCStr("HT"));}),_nT=[1,_nS,_nR],_nU=[1,_n7,_nT],_nV=[1,_n6,_nU],_nW=[1,_n5,_nV],_nX=new T(function(){return B(unCStr("ENQ"));}),_nY=[1,_nX,_nW],_nZ=new T(function(){return B(unCStr("EOT"));}),_o0=[1,_nZ,_nY],_o1=new T(function(){return B(unCStr("ETX"));}),_o2=[1,_o1,_o0],_o3=new T(function(){return B(unCStr("STX"));}),_o4=[1,_o3,_o2],_o5=new T(function(){return B(unCStr("SOH"));}),_o6=[1,_o5,_o4],_o7=new T(function(){return B(unCStr("NUL"));}),_o8=[1,_o7,_o6],_o9=92,_oa=new T(function(){return B(unCStr("\\DEL"));}),_ob=new T(function(){return B(unCStr("\\a"));}),_oc=new T(function(){return B(unCStr("\\\\"));}),_od=new T(function(){return B(unCStr("\\SO"));}),_oe=new T(function(){return B(unCStr("\\r"));}),_of=new T(function(){return B(unCStr("\\f"));}),_og=new T(function(){return B(unCStr("\\v"));}),_oh=new T(function(){return B(unCStr("\\n"));}),_oi=new T(function(){return B(unCStr("\\t"));}),_oj=new T(function(){return B(unCStr("\\b"));}),_ok=function(_ol,_om){if(_ol<=127){var _on=E(_ol);switch(_on){case 92:return new F(function(){return _G(_oc,_om);});break;case 127:return new F(function(){return _G(_oa,_om);});break;default:if(_on<32){var _oo=E(_on);switch(_oo){case 7:return new F(function(){return _G(_ob,_om);});break;case 8:return new F(function(){return _G(_oj,_om);});break;case 9:return new F(function(){return _G(_oi,_om);});break;case 10:return new F(function(){return _G(_oh,_om);});break;case 11:return new F(function(){return _G(_og,_om);});break;case 12:return new F(function(){return _G(_of,_om);});break;case 13:return new F(function(){return _G(_oe,_om);});break;case 14:var _op=new T(function(){var _oq=E(_om);if(!_oq[0]){return [0];}else{if(E(_oq[1])==72){return B(unAppCStr("\\&",_oq));}else{return E(_oq);}}},1);return new F(function(){return _G(_od,_op);});break;default:var _or=new T(function(){return B(_Y(_o8,_oo));});return new F(function(){return _G([1,_o9,_or],_om);});}}else{return [1,_on,_om];}}}else{var _os=new T(function(){var _ot=jsShowI(_ol),_ou=new T(function(){var _ov=E(_om);if(!_ov[0]){return [0];}else{var _ow=E(_ov[1]);if(_ow<48){return E(_ov);}else{if(_ow>57){return E(_ov);}else{return B(unAppCStr("\\&",_ov));}}}},1);return B(_G(fromJSStr(_ot),_ou));});return [1,_o9,_os];}},_ox=new T(function(){return B(unCStr("\\\""));}),_oy=function(_oz,_oA){var _oB=E(_oz);if(!_oB[0]){return E(_oA);}else{var _oC=_oB[2],_oD=E(_oB[1]);if(_oD==34){var _oE=new T(function(){return B(_oy(_oC,_oA));},1);return new F(function(){return _G(_ox,_oE);});}else{var _oF=new T(function(){return B(_oy(_oC,_oA));});return new F(function(){return _ok(_oD,_oF);});}}},_oG=new T(function(){return B(_oy(_n2,_n4));}),_oH=[1,_n3,_oG],_oI=new T(function(){return B(unCStr("Unparsed"));}),_oJ=[1,_n3,_2D],_oK=new T(function(){return B(_oy(_oI,_oJ));}),_oL=[1,_n3,_oK],_oM=new T(function(){return B(unCStr("IndianRoller2.jpg"));}),_oN=[0,_2h,_2D],_oO=function(_){return new F(function(){return jsMkStdout();});},_oP=new T(function(){return B(_8d(_oO));}),_oQ=function(_){var _oR=jsFind("filePath");if(!_oR[0]){return new F(function(){return die(_mA);});}else{var _oS=jsFind("loadPath");if(!_oS[0]){return new F(function(){return die(_mD);});}else{var _oT=nMV(_mx),_oU=_oT,_oV=nMV(_oN),_oW=_oV,_oX=B(A(_3,[_5z,_oM,_])),_oY=nMV(_oX),_oZ=_oY,_p0=nMV(_oM),_p1=_p0,_p2=B(A(_hw,[_5z,_hD,_])),_p3=E(_p2);if(!_p3[0]){return new F(function(){return die(_mG);});}else{var _p4=B(A(_hw,[_5z,_hB,_])),_p5=E(_p4);if(!_p5[0]){return new F(function(){return die(_mJ);});}else{var _p6=_oW,_p7=_oZ,_p8=function(_){return new F(function(){return _i3(_p6,_oU,_p7,_);});},_p9=B(_kk(_oU,_p3[1],_p8,_)),_pa=B(_lJ(_p6,_p5[1],_p8,_)),_pb=function(_pc,_){var _pd=String(E(_pc)),_pe=jsParseJSON(_pd);if(!_pe[0]){var _pf=B(_mk(_oP,_oH,_)),_pg=B(_mk(_oP,fromJSStr(_pd),_));return _8h;}else{var _ph=B(_2V(_pe[1]));if(!_ph[0]){var _pi=B(_mk(_oP,_oL,_)),_pj=B(_mk(_oP,fromJSStr(_pd),_));return _8h;}else{var _pk=_ph[1],_pl=new T(function(){return E(E(_pk)[1]);}),_=wMV(_oU,_pl),_pm=new T(function(){return E(E(_pk)[2]);}),_=wMV(_oW,_pm);return _8h;}}},_pn=__createJSFunc(2,E(_pb)),_po=(function(s,f){Haste[s] = f;}),_pp=_po,_pq=new T(function(){return E(_pp);}),_pr=E(_pq)("processDump",_pn),_ps=function(_pt,_){var _pu=E(_pt),_pv=toJSStr(_n1),_pw=E(_md)(_pv),_px=_pw,_py=new T(function(){var _pz=String(_px);return fromJSStr(_pz);}),_pA=B(A(_3,[_5z,_py,_])),_=wMV(_oZ,_pA),_pB=E(_me)(_pv),_pC=_pB,_pD=new T(function(){var _pE=String(_pC);return fromJSStr(_pE);}),_=wMV(_p1,_pD),_pF=jsFind(toJSStr(E(_hM)));if(!_pF[0]){return new F(function(){return die(_mU);});}else{var _pG=new T(function(){return B(_G(_pD,_n0));}),_pH=B(A(_eu,[_s,_5z,_pF[1],_mY,_pG,_])),_pI=jsFind(toJSStr(E(_hN)));if(!_pI[0]){return new F(function(){return die(_mX);});}else{var _pJ=new T(function(){return B(_G(_pD,_mZ));}),_pK=B(A(_eu,[_s,_5z,_pI[1],_mY,_pJ,_]));return new F(function(){return _i3(_p6,_oU,_p7,_);});}}},_pL=B(A(_bd,[_5A,_s,_n,_oR[1],_jJ,_ps,_])),_pM=B(A(_bd,[_5A,_s,_n,_oS[1],_jJ,_mM,_]));return new F(function(){return _i3(_p6,_oU,_p7,_);});}}}}},_pN=function(_){return new F(function(){return _oQ(_);});};
var hasteMain = function() {B(A(_pN, [0]));};window.onload = hasteMain;