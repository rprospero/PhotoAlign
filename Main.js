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

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
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

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
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

var _0="src",_1=(function(e,p,v){e[p] = v;}),_2=function(_3){return E(E(_3)[2]);},_4=(function(t){return document.createElement(t);}),_5=function(_6,_7){return new F(function(){return A(_2,[_6,function(_){var _8=E(_4)("img"),_9=E(_1)(_8,E(_0),toJSStr(E(_7)));return _8;}]);});},_a=0,_b=function(_){return _a;},_c=function(_d,_e,_){return new F(function(){return _b(_);});},_f="scroll",_g="submit",_h="blur",_i="focus",_j="change",_k="unload",_l="load",_m=function(_n){switch(E(_n)){case 0:return E(_l);case 1:return E(_k);case 2:return E(_j);case 3:return E(_i);case 4:return E(_h);case 5:return E(_g);default:return E(_f);}},_o=[0,_m,_c],_p="metaKey",_q="shiftKey",_r="altKey",_s="ctrlKey",_t="keyCode",_u=function(_v,_){var _w=_v[E(_t)],_x=_v[E(_s)],_y=_v[E(_r)],_z=_v[E(_q)],_A=_v[E(_p)];return new T(function(){var _B=Number(_w),_C=jsTrunc(_B);return [0,_C,E(_x),E(_y),E(_z),E(_A)];});},_D=function(_E,_F,_){return new F(function(){return _u(E(_F),_);});},_G="keydown",_H="keyup",_I="keypress",_J=function(_K){switch(E(_K)){case 0:return E(_I);case 1:return E(_H);default:return E(_G);}},_L=[0,_J,_D],_M=(function(e){return e.getContext('2d');}),_N=(function(e){return !!e.getContext;}),_O=function(_P,_){return [1,_P];},_Q=function(_R){return E(_R);},_S=[0,_Q,_O],_T=function(_U){return E(E(_U)[1]);},_V=function(_W,_X){return (!B(A(_T,[_Y,_W,_X])))?true:false;},_Z=function(_10,_11){var _12=strEq(E(_10),E(_11));return (E(_12)==0)?false:true;},_13=function(_14,_15){return new F(function(){return _Z(_14,_15);});},_Y=new T(function(){return [0,_13,_V];}),_16=function(_17,_18){var _19=E(_17);return (_19[0]==0)?E(_18):[1,_19[1],new T(function(){return B(_16(_19[2],_18));})];},_1a=function(_1b,_1c){var _1d=jsShowI(_1b);return new F(function(){return _16(fromJSStr(_1d),_1c);});},_1e=41,_1f=40,_1g=function(_1h,_1i,_1j){if(_1i>=0){return new F(function(){return _1a(_1i,_1j);});}else{if(_1h<=6){return new F(function(){return _1a(_1i,_1j);});}else{return [1,_1f,new T(function(){var _1k=jsShowI(_1i);return B(_16(fromJSStr(_1k),[1,_1e,_1j]));})];}}},_1l=[0],_1m=function(_1n,_1o){var _1p=new T(function(){return B(_1g(0,_1o,_1l));});if(_1o>=0){var _1q=function(_1r,_1s){var _1t=function(_1u){var _1v=E(_1s);if(!_1v[0]){return [0,new T(function(){var _1w=new T(function(){var _1x=new T(function(){return B(unAppCStr(", length=",new T(function(){return B(_1g(0,_1o-_1r|0,_1l));})));},1);return B(_16(_1p,_1x));});return B(unAppCStr("index too large, index=",_1w));})];}else{return new F(function(){return _1q(_1r-1|0,_1v[2]);});}};if(!E(_1r)){var _1y=E(_1s);if(!_1y[0]){return new F(function(){return _1t(_);});}else{return [1,_1y[1]];}}else{return new F(function(){return _1t(_);});}};return new F(function(){return _1q(_1o,_1n);});}else{return [0,new T(function(){return B(unAppCStr("index must not be negative, index=",_1p));})];}},_1z=[1,_1l],_1A=function(_1B){var _1C=E(_1B);if(!_1C[0]){return E(_1z);}else{var _1D=E(_1C[1]);if(_1D[0]==3){var _1E=E(_1D[1]);if(!_1E[0]){return [0];}else{var _1F=E(_1E[1]);if(!_1F[0]){var _1G=B(_1m(_1E,1));if(!_1G[0]){return [0];}else{var _1H=E(_1G[1]);if(!_1H[0]){var _1I=B(_1A(_1C[2]));return (_1I[0]==0)?[0]:[1,[1,[0,_1F[1],_1H[1]],_1I[1]]];}else{return [0];}}}else{return [0];}}}else{return [0];}}},_1J=function(_1K){var _1L=E(_1K);if(_1L[0]==3){var _1M=B(_1A(_1L[1]));if(!_1M[0]){return [0];}else{var _1N=E(_1M[1]);if(!_1N[0]){return [0];}else{var _1O=B(_1m(_1N,1));if(!_1O[0]){return [0];}else{var _1P=B(_1m(_1N,2));if(!_1P[0]){return [0];}else{var _1Q=B(_1m(_1N,3));return (_1Q[0]==0)?[0]:[1,[0,_1N[1],_1O[1],_1P[1],_1Q[1]]];}}}}}else{return [0];}},_1R="box",_1S="mouse",_1T="corner",_1U="Dragging",_1V=[0],_1W=[1,_1V],_1X="Free",_1Y="state",_1Z=1,_20=[1,_1Z],_21=0,_22=[1,_21],_23=3,_24=[1,_23],_25=2,_26=[1,_25],_27=new T(function(){return B(unCStr("SW"));}),_28=new T(function(){return B(unCStr("SE"));}),_29=new T(function(){return B(unCStr("NW"));}),_2a=new T(function(){return B(unCStr("NE"));}),_2b=function(_2c,_2d){while(1){var _2e=E(_2c);if(!_2e[0]){return (E(_2d)[0]==0)?true:false;}else{var _2f=E(_2d);if(!_2f[0]){return false;}else{if(E(_2e[1])!=E(_2f[1])){return false;}else{_2c=_2e[2];_2d=_2f[2];continue;}}}}},_2g=function(_2h){var _2i=E(_2h);if(_2i[0]==1){var _2j=fromJSStr(_2i[1]);return (!B(_2b(_2j,_2a)))?(!B(_2b(_2j,_29)))?(!B(_2b(_2j,_28)))?(!B(_2b(_2j,_27)))?[0]:E(_26):E(_24):E(_22):E(_20);}else{return [0];}},_2k=function(_2l,_2m,_2n){while(1){var _2o=E(_2n);if(!_2o[0]){return [0];}else{var _2p=E(_2o[1]);if(!B(A(_T,[_2l,_2m,_2p[1]]))){_2n=_2o[2];continue;}else{return [1,_2p[2]];}}}},_2q=function(_2r){var _2s=E(_2r);if(_2s[0]==4){var _2t=_2s[1],_2u=B(_2k(_Y,_1Y,_2t));if(!_2u[0]){return [0];}else{var _2v=E(_2u[1]);if(_2v[0]==1){var _2w=_2v[1],_2x=strEq(_2w,E(_1X));if(!E(_2x)){var _2y=strEq(_2w,E(_1U));if(!E(_2y)){return [0];}else{var _2z=B(_2k(_Y,_1T,_2t));if(!_2z[0]){return [0];}else{var _2A=B(_2g(_2z[1]));return (_2A[0]==0)?[0]:[1,[1,_2A[1]]];}}}else{return E(_1W);}}else{return [0];}}}else{return [0];}},_2B=function(_2C){var _2D=E(_2C);if(_2D[0]==4){var _2E=_2D[1],_2F=B(_2k(_Y,_1S,_2E));if(!_2F[0]){return [0];}else{var _2G=B(_2q(_2F[1]));if(!_2G[0]){return [0];}else{var _2H=B(_2k(_Y,_1R,_2E));if(!_2H[0]){return [0];}else{var _2I=B(_1J(_2H[1]));return (_2I[0]==0)?[0]:[1,[0,_2G[1],_2I[1]]];}}}}else{return [0];}},_2J=function(_2K){return [0,E(_2K)];},_2L=function(_2M){var _2N=E(_2M);return (_2N[0]==0)?[1,_2N[1]]:[0];},_2O=[0,_2J,_2L],_2P=1,_2Q=[1,_2P],_2R=0,_2S=[1,_2R],_2T=new T(function(){return B(unCStr("Top"));}),_2U=new T(function(){return B(unCStr("Bottom"));}),_2V=function(_2W){var _2X=E(_2W);if(_2X[0]==1){var _2Y=fromJSStr(_2X[1]);return (!B(_2b(_2Y,_2U)))?(!B(_2b(_2Y,_2T)))?[0]:E(_2S):E(_2Q);}else{return [0];}},_2Z=1,_30=[1,_2Z],_31=0,_32=[1,_31],_33=new T(function(){return B(unCStr("Free"));}),_34=new T(function(){return B(unCStr("Dragging"));}),_35=function(_36){var _37=E(_36);if(_37[0]==1){var _38=fromJSStr(_37[1]);return (!B(_2b(_38,_34)))?(!B(_2b(_38,_33)))?[0]:E(_32):E(_30);}else{return [0];}},_39="title",_3a="points",_3b=function(_3c){var _3d=E(_3c);if(_3d[0]==4){var _3e=_3d[1],_3f=B(_2k(_Y,_3a,_3e));if(!_3f[0]){return [0];}else{var _3g=E(_3f[1]);if(_3g[0]==3){var _3h=E(_3g[1]);if(!_3h[0]){return [0];}else{var _3i=E(_3h[1]);if(_3i[0]==3){var _3j=E(_3i[1]);if(!_3j[0]){return [0];}else{var _3k=E(_3j[1]);if(!_3k[0]){var _3l=B(_1m(_3j,1));if(!_3l[0]){return [0];}else{var _3m=E(_3l[1]);if(!_3m[0]){var _3n=B(_1m(_3h,1));if(!_3n[0]){return [0];}else{var _3o=E(_3n[1]);if(_3o[0]==3){var _3p=E(_3o[1]);if(!_3p[0]){return [0];}else{var _3q=E(_3p[1]);if(!_3q[0]){var _3r=B(_1m(_3p,1));if(!_3r[0]){return [0];}else{var _3s=E(_3r[1]);if(!_3s[0]){var _3t=B(_2k(_Y,_39,_3e));if(!_3t[0]){return [0];}else{var _3u=E(_3t[1]);return (_3u[0]==1)?[1,[0,[0,_3k[1],_3m[1]],[0,_3q[1],_3s[1]],new T(function(){return fromJSStr(_3u[1]);})]]:[0];}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}},_3v=function(_3w){var _3x=new T(function(){var _3y=E(E(_3w)[2]);return [3,[1,new T(function(){return B(_2J(_3y[1]));}),[1,new T(function(){return B(_2J(_3y[2]));}),_1l]]];}),_3z=new T(function(){var _3A=E(E(_3w)[1]);return [3,[1,new T(function(){return B(_2J(_3A[1]));}),[1,new T(function(){return B(_2J(_3A[2]));}),_1l]]];});return [1,[0,_39,new T(function(){return [1,toJSStr(E(E(_3w)[3]))];})],[1,[0,_3a,[3,[1,_3z,[1,_3x,_1l]]]],_1l]];},_3B=function(_3C){return [4,E(B(_3v(_3C)))];},_3D=[0,_3B,_3b],_3E=[1,_1l],_3F=function(_3G){return E(E(_3G)[2]);},_3H=function(_3I,_3J){var _3K=E(_3J);if(_3K[0]==3){var _3L=new T(function(){return B(_3F(_3I));}),_3M=function(_3N){var _3O=E(_3N);if(!_3O[0]){return E(_3E);}else{var _3P=B(A(_3L,[_3O[1]]));if(!_3P[0]){return [0];}else{var _3Q=B(_3M(_3O[2]));return (_3Q[0]==0)?[0]:[1,[1,_3P[1],_3Q[1]]];}}};return new F(function(){return _3M(_3K[1]);});}else{return [0];}},_3R="rotations",_3S=0.1,_3T="step",_3U="choice",_3V="offset",_3W="bottom",_3X="top",_3Y="scans",_3Z="mouse",_40=function(_41){var _42=E(_41);if(_42[0]==4){var _43=_42[1],_44=B(_2k(_Y,_3Z,_43));if(!_44[0]){return [0];}else{var _45=B(_35(_44[1]));if(!_45[0]){return [0];}else{var _46=_45[1],_47=B(_2k(_Y,_3Y,_43));if(!_47[0]){return [0];}else{var _48=B(_3H(_3D,_47[1]));if(!_48[0]){return [0];}else{var _49=_48[1],_4a=B(_2k(_Y,_3X,_43));if(!_4a[0]){return [0];}else{var _4b=E(_4a[1]);if(!_4b[0]){var _4c=_4b[1],_4d=B(_2k(_Y,_3W,_43));if(!_4d[0]){return [0];}else{var _4e=E(_4d[1]);if(!_4e[0]){var _4f=_4e[1],_4g=B(_2k(_Y,_3V,_43));if(!_4g[0]){return [0];}else{var _4h=E(_4g[1]);if(!_4h[0]){var _4i=_4h[1],_4j=B(_2k(_Y,_3U,_43));if(!_4j[0]){return [0];}else{var _4k=B(_2V(_4j[1]));if(!_4k[0]){return [0];}else{var _4l=_4k[1],_4m=B(_2k(_Y,_3T,_43));if(!_4m[0]){var _4n=B(_2k(_Y,_3R,_43));if(!_4n[0]){return [0];}else{var _4o=B(_3H(_2O,_4n[1]));return (_4o[0]==0)?[0]:[1,[0,_46,_49,_4c,_4f,_4i,_4l,_3S,_4o[1]]];}}else{var _4p=E(_4m[1]);if(!_4p[0]){var _4q=B(_2k(_Y,_3R,_43));if(!_4q[0]){return [0];}else{var _4r=B(_3H(_2O,_4q[1]));return (_4r[0]==0)?[0]:[1,[0,_46,_49,_4c,_4f,_4i,_4l,_4p[1],_4r[1]]];}}else{return [0];}}}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}}}}}else{return [0];}},_4s="scans",_4t="calib",_4u=function(_4v){var _4w=E(_4v);if(_4w[0]==4){var _4x=_4w[1],_4y=B(_2k(_Y,_4t,_4x));if(!_4y[0]){return [0];}else{var _4z=B(_2B(_4y[1]));if(!_4z[0]){return [0];}else{var _4A=B(_2k(_Y,_4s,_4x));if(!_4A[0]){return [0];}else{var _4B=B(_40(_4A[1]));return (_4B[0]==0)?[0]:[1,[0,_4z[1],_4B[1]]];}}}}else{return [0];}},_4C=function(_4D,_4E,_){var _4F=B(A(_4D,[_])),_4G=B(A(_4E,[_]));return _4F;},_4H=function(_4I,_4J,_){var _4K=B(A(_4I,[_])),_4L=B(A(_4J,[_]));return new T(function(){return B(A(_4K,[_4L]));});},_4M=function(_4N,_4O,_){var _4P=B(A(_4O,[_]));return _4N;},_4Q=function(_4R,_4S,_){var _4T=B(A(_4S,[_]));return new T(function(){return B(A(_4R,[_4T]));});},_4U=[0,_4Q,_4M],_4V=function(_4W,_){return _4W;},_4X=function(_4Y,_4Z,_){var _50=B(A(_4Y,[_]));return new F(function(){return A(_4Z,[_]);});},_51=[0,_4U,_4V,_4H,_4X,_4C],_52=function(_53,_54,_){var _55=B(A(_53,[_]));return new F(function(){return A(_54,[_55,_]);});},_56=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_57=new T(function(){return B(unCStr("base"));}),_58=new T(function(){return B(unCStr("IOException"));}),_59=new T(function(){var _5a=hs_wordToWord64(4053623282),_5b=hs_wordToWord64(3693590983);return [0,_5a,_5b,[0,_5a,_5b,_57,_56,_58],_1l,_1l];}),_5c=function(_5d){return E(_59);},_5e=function(_5f){return E(E(_5f)[1]);},_5g=function(_5h,_5i,_5j){var _5k=B(A(_5h,[_])),_5l=B(A(_5i,[_])),_5m=hs_eqWord64(_5k[1],_5l[1]);if(!_5m){return [0];}else{var _5n=hs_eqWord64(_5k[2],_5l[2]);return (!_5n)?[0]:[1,_5j];}},_5o=function(_5p){var _5q=E(_5p);return new F(function(){return _5g(B(_5e(_5q[1])),_5c,_5q[2]);});},_5r=new T(function(){return B(unCStr(": "));}),_5s=new T(function(){return B(unCStr(")"));}),_5t=new T(function(){return B(unCStr(" ("));}),_5u=new T(function(){return B(unCStr("interrupted"));}),_5v=new T(function(){return B(unCStr("system error"));}),_5w=new T(function(){return B(unCStr("unsatisified constraints"));}),_5x=new T(function(){return B(unCStr("user error"));}),_5y=new T(function(){return B(unCStr("permission denied"));}),_5z=new T(function(){return B(unCStr("illegal operation"));}),_5A=new T(function(){return B(unCStr("end of file"));}),_5B=new T(function(){return B(unCStr("resource exhausted"));}),_5C=new T(function(){return B(unCStr("resource busy"));}),_5D=new T(function(){return B(unCStr("does not exist"));}),_5E=new T(function(){return B(unCStr("already exists"));}),_5F=new T(function(){return B(unCStr("resource vanished"));}),_5G=new T(function(){return B(unCStr("timeout"));}),_5H=new T(function(){return B(unCStr("unsupported operation"));}),_5I=new T(function(){return B(unCStr("hardware fault"));}),_5J=new T(function(){return B(unCStr("inappropriate type"));}),_5K=new T(function(){return B(unCStr("invalid argument"));}),_5L=new T(function(){return B(unCStr("failed"));}),_5M=new T(function(){return B(unCStr("protocol error"));}),_5N=function(_5O,_5P){switch(E(_5O)){case 0:return new F(function(){return _16(_5E,_5P);});break;case 1:return new F(function(){return _16(_5D,_5P);});break;case 2:return new F(function(){return _16(_5C,_5P);});break;case 3:return new F(function(){return _16(_5B,_5P);});break;case 4:return new F(function(){return _16(_5A,_5P);});break;case 5:return new F(function(){return _16(_5z,_5P);});break;case 6:return new F(function(){return _16(_5y,_5P);});break;case 7:return new F(function(){return _16(_5x,_5P);});break;case 8:return new F(function(){return _16(_5w,_5P);});break;case 9:return new F(function(){return _16(_5v,_5P);});break;case 10:return new F(function(){return _16(_5M,_5P);});break;case 11:return new F(function(){return _16(_5L,_5P);});break;case 12:return new F(function(){return _16(_5K,_5P);});break;case 13:return new F(function(){return _16(_5J,_5P);});break;case 14:return new F(function(){return _16(_5I,_5P);});break;case 15:return new F(function(){return _16(_5H,_5P);});break;case 16:return new F(function(){return _16(_5G,_5P);});break;case 17:return new F(function(){return _16(_5F,_5P);});break;default:return new F(function(){return _16(_5u,_5P);});}},_5Q=new T(function(){return B(unCStr("}"));}),_5R=new T(function(){return B(unCStr("{handle: "));}),_5S=function(_5T,_5U,_5V,_5W,_5X,_5Y){var _5Z=new T(function(){var _60=new T(function(){var _61=new T(function(){var _62=E(_5W);if(!_62[0]){return E(_5Y);}else{var _63=new T(function(){return B(_16(_62,new T(function(){return B(_16(_5s,_5Y));},1)));},1);return B(_16(_5t,_63));}},1);return B(_5N(_5U,_61));}),_64=E(_5V);if(!_64[0]){return E(_60);}else{return B(_16(_64,new T(function(){return B(_16(_5r,_60));},1)));}}),_65=E(_5X);if(!_65[0]){var _66=E(_5T);if(!_66[0]){return E(_5Z);}else{var _67=E(_66[1]);if(!_67[0]){var _68=new T(function(){var _69=new T(function(){return B(_16(_5Q,new T(function(){return B(_16(_5r,_5Z));},1)));},1);return B(_16(_67[1],_69));},1);return new F(function(){return _16(_5R,_68);});}else{var _6a=new T(function(){var _6b=new T(function(){return B(_16(_5Q,new T(function(){return B(_16(_5r,_5Z));},1)));},1);return B(_16(_67[1],_6b));},1);return new F(function(){return _16(_5R,_6a);});}}}else{return new F(function(){return _16(_65[1],new T(function(){return B(_16(_5r,_5Z));},1));});}},_6c=function(_6d){var _6e=E(_6d);return new F(function(){return _5S(_6e[1],_6e[2],_6e[3],_6e[4],_6e[6],_1l);});},_6f=function(_6g,_6h,_6i){var _6j=E(_6h);return new F(function(){return _5S(_6j[1],_6j[2],_6j[3],_6j[4],_6j[6],_6i);});},_6k=function(_6l,_6m){var _6n=E(_6l);return new F(function(){return _5S(_6n[1],_6n[2],_6n[3],_6n[4],_6n[6],_6m);});},_6o=44,_6p=93,_6q=91,_6r=function(_6s,_6t,_6u){var _6v=E(_6t);if(!_6v[0]){return new F(function(){return unAppCStr("[]",_6u);});}else{var _6w=new T(function(){var _6x=new T(function(){var _6y=function(_6z){var _6A=E(_6z);if(!_6A[0]){return [1,_6p,_6u];}else{var _6B=new T(function(){return B(A(_6s,[_6A[1],new T(function(){return B(_6y(_6A[2]));})]));});return [1,_6o,_6B];}};return B(_6y(_6v[2]));});return B(A(_6s,[_6v[1],_6x]));});return [1,_6q,_6w];}},_6C=function(_6D,_6E){return new F(function(){return _6r(_6k,_6D,_6E);});},_6F=[0,_6f,_6c,_6C],_6G=new T(function(){return [0,_5c,_6F,_6H,_5o,_6c];}),_6H=function(_6I){return [0,_6G,_6I];},_6J=[0],_6K=7,_6L=function(_6M){return [0,_6J,_6K,_1l,_6M,_6J,_6J];},_6N=function(_6O,_){var _6P=new T(function(){return B(_6H(new T(function(){return B(_6L(_6O));})));});return new F(function(){return die(_6P);});},_6Q=[0,_51,_52,_4X,_4V,_6N],_6R=[0,_6Q,_Q],_6S=[0,_6R,_4V],_6T=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6U=new T(function(){return B(unCStr("base"));}),_6V=new T(function(){return B(unCStr("PatternMatchFail"));}),_6W=new T(function(){var _6X=hs_wordToWord64(18445595),_6Y=hs_wordToWord64(52003073);return [0,_6X,_6Y,[0,_6X,_6Y,_6U,_6T,_6V],_1l,_1l];}),_6Z=function(_70){return E(_6W);},_71=function(_72){var _73=E(_72);return new F(function(){return _5g(B(_5e(_73[1])),_6Z,_73[2]);});},_74=function(_75){return E(E(_75)[1]);},_76=function(_77){return [0,_78,_77];},_79=function(_7a,_7b){return new F(function(){return _16(E(_7a)[1],_7b);});},_7c=function(_7d,_7e){return new F(function(){return _6r(_79,_7d,_7e);});},_7f=function(_7g,_7h,_7i){return new F(function(){return _16(E(_7h)[1],_7i);});},_7j=[0,_7f,_74,_7c],_78=new T(function(){return [0,_6Z,_7j,_76,_71,_74];}),_7k=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_7l=function(_7m){return E(E(_7m)[3]);},_7n=function(_7o,_7p){return new F(function(){return die(new T(function(){return B(A(_7l,[_7p,_7o]));}));});},_7q=function(_7r,_7s){return new F(function(){return _7n(_7r,_7s);});},_7t=function(_7u,_7v){var _7w=E(_7v);if(!_7w[0]){return [0,_1l,_1l];}else{var _7x=_7w[1];if(!B(A(_7u,[_7x]))){return [0,_1l,_7w];}else{var _7y=new T(function(){var _7z=B(_7t(_7u,_7w[2]));return [0,_7z[1],_7z[2]];});return [0,[1,_7x,new T(function(){return E(E(_7y)[1]);})],new T(function(){return E(E(_7y)[2]);})];}}},_7A=32,_7B=new T(function(){return B(unCStr("\n"));}),_7C=function(_7D){return (E(_7D)==124)?false:true;},_7E=function(_7F,_7G){var _7H=B(_7t(_7C,B(unCStr(_7F)))),_7I=_7H[1],_7J=function(_7K,_7L){var _7M=new T(function(){var _7N=new T(function(){return B(_16(_7G,new T(function(){return B(_16(_7L,_7B));},1)));});return B(unAppCStr(": ",_7N));},1);return new F(function(){return _16(_7K,_7M);});},_7O=E(_7H[2]);if(!_7O[0]){return new F(function(){return _7J(_7I,_1l);});}else{if(E(_7O[1])==124){return new F(function(){return _7J(_7I,[1,_7A,_7O[2]]);});}else{return new F(function(){return _7J(_7I,_1l);});}}},_7P=function(_7Q){return new F(function(){return _7q([0,new T(function(){return B(_7E(_7Q,_7k));})],_78);});},_7R=new T(function(){return B(_7P("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_7S=function(_7T,_7U){while(1){var _7V=B((function(_7W,_7X){var _7Y=E(_7W);switch(_7Y[0]){case 0:var _7Z=E(_7X);if(!_7Z[0]){return [0];}else{_7T=B(A(_7Y[1],[_7Z[1]]));_7U=_7Z[2];return null;}break;case 1:var _80=B(A(_7Y[1],[_7X])),_81=_7X;_7T=_80;_7U=_81;return null;case 2:return [0];case 3:return [1,[0,_7Y[1],_7X],new T(function(){return B(_7S(_7Y[2],_7X));})];default:return E(_7Y[1]);}})(_7T,_7U));if(_7V!=null){return _7V;}}},_82=function(_83,_84){var _85=function(_86){var _87=E(_84);if(_87[0]==3){return [3,_87[1],new T(function(){return B(_82(_83,_87[2]));})];}else{var _88=E(_83);if(_88[0]==2){return E(_87);}else{var _89=E(_87);if(_89[0]==2){return E(_88);}else{var _8a=function(_8b){var _8c=E(_89);if(_8c[0]==4){return [1,function(_8d){return [4,new T(function(){return B(_16(B(_7S(_88,_8d)),_8c[1]));})];}];}else{var _8e=E(_88);if(_8e[0]==1){var _8f=_8e[1],_8g=E(_8c);if(!_8g[0]){return [1,function(_8h){return new F(function(){return _82(B(A(_8f,[_8h])),_8g);});}];}else{return [1,function(_8i){return new F(function(){return _82(B(A(_8f,[_8i])),new T(function(){return B(A(_8g[1],[_8i]));}));});}];}}else{var _8j=E(_8c);if(!_8j[0]){return E(_7R);}else{return [1,function(_8k){return new F(function(){return _82(_8e,new T(function(){return B(A(_8j[1],[_8k]));}));});}];}}}},_8l=E(_88);switch(_8l[0]){case 1:var _8m=E(_89);if(_8m[0]==4){return [1,function(_8n){return [4,new T(function(){return B(_16(B(_7S(B(A(_8l[1],[_8n])),_8n)),_8m[1]));})];}];}else{return new F(function(){return _8a(_);});}break;case 4:var _8o=_8l[1],_8p=E(_89);switch(_8p[0]){case 0:return [1,function(_8q){return [4,new T(function(){return B(_16(_8o,new T(function(){return B(_7S(_8p,_8q));},1)));})];}];case 1:return [1,function(_8r){return [4,new T(function(){return B(_16(_8o,new T(function(){return B(_7S(B(A(_8p[1],[_8r])),_8r));},1)));})];}];default:return [4,new T(function(){return B(_16(_8o,_8p[1]));})];}break;default:return new F(function(){return _8a(_);});}}}}},_8s=E(_83);switch(_8s[0]){case 0:var _8t=E(_84);if(!_8t[0]){return [0,function(_8u){return new F(function(){return _82(B(A(_8s[1],[_8u])),new T(function(){return B(A(_8t[1],[_8u]));}));});}];}else{return new F(function(){return _85(_);});}break;case 3:return [3,_8s[1],new T(function(){return B(_82(_8s[2],_84));})];default:return new F(function(){return _85(_);});}},_8v=new T(function(){return B(unCStr("("));}),_8w=new T(function(){return B(unCStr(")"));}),_8x=function(_8y,_8z){return E(_8y)!=E(_8z);},_8A=function(_8B,_8C){return E(_8B)==E(_8C);},_8D=[0,_8A,_8x],_8E=function(_8F,_8G){while(1){var _8H=E(_8F);if(!_8H[0]){return (E(_8G)[0]==0)?true:false;}else{var _8I=E(_8G);if(!_8I[0]){return false;}else{if(E(_8H[1])!=E(_8I[1])){return false;}else{_8F=_8H[2];_8G=_8I[2];continue;}}}}},_8J=function(_8K,_8L){return (!B(_8E(_8K,_8L)))?true:false;},_8M=[0,_8E,_8J],_8N=function(_8O,_8P){var _8Q=E(_8O);switch(_8Q[0]){case 0:return [0,function(_8R){return new F(function(){return _8N(B(A(_8Q[1],[_8R])),_8P);});}];case 1:return [1,function(_8S){return new F(function(){return _8N(B(A(_8Q[1],[_8S])),_8P);});}];case 2:return [2];case 3:return new F(function(){return _82(B(A(_8P,[_8Q[1]])),new T(function(){return B(_8N(_8Q[2],_8P));}));});break;default:var _8T=function(_8U){var _8V=E(_8U);if(!_8V[0]){return [0];}else{var _8W=E(_8V[1]);return new F(function(){return _16(B(_7S(B(A(_8P,[_8W[1]])),_8W[2])),new T(function(){return B(_8T(_8V[2]));},1));});}},_8X=B(_8T(_8Q[1]));return (_8X[0]==0)?[2]:[4,_8X];}},_8Y=[2],_8Z=function(_90){return [3,_90,_8Y];},_91=function(_92,_93){var _94=E(_92);if(!_94){return new F(function(){return A(_93,[_a]);});}else{var _95=new T(function(){return B(_91(_94-1|0,_93));});return [0,function(_96){return E(_95);}];}},_97=function(_98,_99,_9a){var _9b=new T(function(){return B(A(_98,[_8Z]));}),_9c=function(_9d,_9e,_9f,_9g){while(1){var _9h=B((function(_9i,_9j,_9k,_9l){var _9m=E(_9i);switch(_9m[0]){case 0:var _9n=E(_9j);if(!_9n[0]){return new F(function(){return A(_99,[_9l]);});}else{var _9o=_9k+1|0,_9p=_9l;_9d=B(A(_9m[1],[_9n[1]]));_9e=_9n[2];_9f=_9o;_9g=_9p;return null;}break;case 1:var _9q=B(A(_9m[1],[_9j])),_9r=_9j,_9o=_9k,_9p=_9l;_9d=_9q;_9e=_9r;_9f=_9o;_9g=_9p;return null;case 2:return new F(function(){return A(_99,[_9l]);});break;case 3:var _9s=new T(function(){return B(_8N(_9m,_9l));});return new F(function(){return _91(_9k,function(_9t){return E(_9s);});});break;default:return new F(function(){return _8N(_9m,_9l);});}})(_9d,_9e,_9f,_9g));if(_9h!=null){return _9h;}}};return function(_9u){return new F(function(){return _9c(_9b,_9u,0,_9a);});};},_9v=function(_9w){return new F(function(){return A(_9w,[_1l]);});},_9x=function(_9y,_9z){var _9A=function(_9B){var _9C=E(_9B);if(!_9C[0]){return E(_9v);}else{var _9D=_9C[1];if(!B(A(_9y,[_9D]))){return E(_9v);}else{var _9E=new T(function(){return B(_9A(_9C[2]));}),_9F=function(_9G){var _9H=new T(function(){return B(A(_9E,[function(_9I){return new F(function(){return A(_9G,[[1,_9D,_9I]]);});}]));});return [0,function(_9J){return E(_9H);}];};return E(_9F);}}};return function(_9K){return new F(function(){return A(_9A,[_9K,_9z]);});};},_9L=[6],_9M=new T(function(){return B(unCStr("valDig: Bad base"));}),_9N=new T(function(){return B(err(_9M));}),_9O=function(_9P,_9Q){var _9R=function(_9S,_9T){var _9U=E(_9S);if(!_9U[0]){var _9V=new T(function(){return B(A(_9T,[_1l]));});return function(_9W){return new F(function(){return A(_9W,[_9V]);});};}else{var _9X=E(_9U[1]),_9Y=function(_9Z){var _a0=new T(function(){return B(_9R(_9U[2],function(_a1){return new F(function(){return A(_9T,[[1,_9Z,_a1]]);});}));}),_a2=function(_a3){var _a4=new T(function(){return B(A(_a0,[_a3]));});return [0,function(_a5){return E(_a4);}];};return E(_a2);};switch(E(_9P)){case 8:if(48>_9X){var _a6=new T(function(){return B(A(_9T,[_1l]));});return function(_a7){return new F(function(){return A(_a7,[_a6]);});};}else{if(_9X>55){var _a8=new T(function(){return B(A(_9T,[_1l]));});return function(_a9){return new F(function(){return A(_a9,[_a8]);});};}else{return new F(function(){return _9Y(_9X-48|0);});}}break;case 10:if(48>_9X){var _aa=new T(function(){return B(A(_9T,[_1l]));});return function(_ab){return new F(function(){return A(_ab,[_aa]);});};}else{if(_9X>57){var _ac=new T(function(){return B(A(_9T,[_1l]));});return function(_ad){return new F(function(){return A(_ad,[_ac]);});};}else{return new F(function(){return _9Y(_9X-48|0);});}}break;case 16:if(48>_9X){if(97>_9X){if(65>_9X){var _ae=new T(function(){return B(A(_9T,[_1l]));});return function(_af){return new F(function(){return A(_af,[_ae]);});};}else{if(_9X>70){var _ag=new T(function(){return B(A(_9T,[_1l]));});return function(_ah){return new F(function(){return A(_ah,[_ag]);});};}else{return new F(function(){return _9Y((_9X-65|0)+10|0);});}}}else{if(_9X>102){if(65>_9X){var _ai=new T(function(){return B(A(_9T,[_1l]));});return function(_aj){return new F(function(){return A(_aj,[_ai]);});};}else{if(_9X>70){var _ak=new T(function(){return B(A(_9T,[_1l]));});return function(_al){return new F(function(){return A(_al,[_ak]);});};}else{return new F(function(){return _9Y((_9X-65|0)+10|0);});}}}else{return new F(function(){return _9Y((_9X-97|0)+10|0);});}}}else{if(_9X>57){if(97>_9X){if(65>_9X){var _am=new T(function(){return B(A(_9T,[_1l]));});return function(_an){return new F(function(){return A(_an,[_am]);});};}else{if(_9X>70){var _ao=new T(function(){return B(A(_9T,[_1l]));});return function(_ap){return new F(function(){return A(_ap,[_ao]);});};}else{return new F(function(){return _9Y((_9X-65|0)+10|0);});}}}else{if(_9X>102){if(65>_9X){var _aq=new T(function(){return B(A(_9T,[_1l]));});return function(_ar){return new F(function(){return A(_ar,[_aq]);});};}else{if(_9X>70){var _as=new T(function(){return B(A(_9T,[_1l]));});return function(_at){return new F(function(){return A(_at,[_as]);});};}else{return new F(function(){return _9Y((_9X-65|0)+10|0);});}}}else{return new F(function(){return _9Y((_9X-97|0)+10|0);});}}}else{return new F(function(){return _9Y(_9X-48|0);});}}break;default:return E(_9N);}}},_au=function(_av){var _aw=E(_av);if(!_aw[0]){return [2];}else{return new F(function(){return A(_9Q,[_aw]);});}};return function(_ax){return new F(function(){return A(_9R,[_ax,_Q,_au]);});};},_ay=16,_az=8,_aA=function(_aB){var _aC=function(_aD){return new F(function(){return A(_aB,[[5,[0,_az,_aD]]]);});},_aE=function(_aF){return new F(function(){return A(_aB,[[5,[0,_ay,_aF]]]);});},_aG=function(_aH){switch(E(_aH)){case 79:return [1,B(_9O(_az,_aC))];case 88:return [1,B(_9O(_ay,_aE))];case 111:return [1,B(_9O(_az,_aC))];case 120:return [1,B(_9O(_ay,_aE))];default:return [2];}};return function(_aI){return (E(_aI)==48)?[0,_aG]:[2];};},_aJ=function(_aK){return [0,B(_aA(_aK))];},_aL=function(_aM){return new F(function(){return A(_aM,[_6J]);});},_aN=function(_aO){return new F(function(){return A(_aO,[_6J]);});},_aP=10,_aQ=[0,1],_aR=[0,2147483647],_aS=function(_aT,_aU){while(1){var _aV=E(_aT);if(!_aV[0]){var _aW=_aV[1],_aX=E(_aU);if(!_aX[0]){var _aY=_aX[1],_aZ=addC(_aW,_aY);if(!E(_aZ[2])){return [0,_aZ[1]];}else{_aT=[1,I_fromInt(_aW)];_aU=[1,I_fromInt(_aY)];continue;}}else{_aT=[1,I_fromInt(_aW)];_aU=_aX;continue;}}else{var _b0=E(_aU);if(!_b0[0]){_aT=_aV;_aU=[1,I_fromInt(_b0[1])];continue;}else{return [1,I_add(_aV[1],_b0[1])];}}}},_b1=new T(function(){return B(_aS(_aR,_aQ));}),_b2=function(_b3){var _b4=E(_b3);if(!_b4[0]){var _b5=E(_b4[1]);return (_b5==(-2147483648))?E(_b1):[0, -_b5];}else{return [1,I_negate(_b4[1])];}},_b6=[0,10],_b7=function(_b8,_b9){while(1){var _ba=E(_b8);if(!_ba[0]){return E(_b9);}else{var _bb=_b9+1|0;_b8=_ba[2];_b9=_bb;continue;}}},_bc=function(_bd,_be){var _bf=E(_be);return (_bf[0]==0)?[0]:[1,new T(function(){return B(A(_bd,[_bf[1]]));}),new T(function(){return B(_bc(_bd,_bf[2]));})];},_bg=function(_bh){return [0,_bh];},_bi=function(_bj){return new F(function(){return _bg(E(_bj));});},_bk=new T(function(){return B(unCStr("this should not happen"));}),_bl=new T(function(){return B(err(_bk));}),_bm=function(_bn,_bo){while(1){var _bp=E(_bn);if(!_bp[0]){var _bq=_bp[1],_br=E(_bo);if(!_br[0]){var _bs=_br[1];if(!(imul(_bq,_bs)|0)){return [0,imul(_bq,_bs)|0];}else{_bn=[1,I_fromInt(_bq)];_bo=[1,I_fromInt(_bs)];continue;}}else{_bn=[1,I_fromInt(_bq)];_bo=_br;continue;}}else{var _bt=E(_bo);if(!_bt[0]){_bn=_bp;_bo=[1,I_fromInt(_bt[1])];continue;}else{return [1,I_mul(_bp[1],_bt[1])];}}}},_bu=function(_bv,_bw){var _bx=E(_bw);if(!_bx[0]){return [0];}else{var _by=E(_bx[2]);return (_by[0]==0)?E(_bl):[1,B(_aS(B(_bm(_bx[1],_bv)),_by[1])),new T(function(){return B(_bu(_bv,_by[2]));})];}},_bz=[0,0],_bA=function(_bB,_bC,_bD){while(1){var _bE=B((function(_bF,_bG,_bH){var _bI=E(_bH);if(!_bI[0]){return E(_bz);}else{if(!E(_bI[2])[0]){return E(_bI[1]);}else{var _bJ=E(_bG);if(_bJ<=40){var _bK=_bz,_bL=_bI;while(1){var _bM=E(_bL);if(!_bM[0]){return E(_bK);}else{var _bN=B(_aS(B(_bm(_bK,_bF)),_bM[1]));_bK=_bN;_bL=_bM[2];continue;}}}else{var _bO=B(_bm(_bF,_bF));if(!(_bJ%2)){var _bP=B(_bu(_bF,_bI));_bB=_bO;_bC=quot(_bJ+1|0,2);_bD=_bP;return null;}else{var _bP=B(_bu(_bF,[1,_bz,_bI]));_bB=_bO;_bC=quot(_bJ+1|0,2);_bD=_bP;return null;}}}}})(_bB,_bC,_bD));if(_bE!=null){return _bE;}}},_bQ=function(_bR,_bS){return new F(function(){return _bA(_bR,new T(function(){return B(_b7(_bS,0));},1),B(_bc(_bi,_bS)));});},_bT=function(_bU){var _bV=new T(function(){var _bW=new T(function(){var _bX=function(_bY){return new F(function(){return A(_bU,[[1,new T(function(){return B(_bQ(_b6,_bY));})]]);});};return [1,B(_9O(_aP,_bX))];}),_bZ=function(_c0){if(E(_c0)==43){var _c1=function(_c2){return new F(function(){return A(_bU,[[1,new T(function(){return B(_bQ(_b6,_c2));})]]);});};return [1,B(_9O(_aP,_c1))];}else{return [2];}},_c3=function(_c4){if(E(_c4)==45){var _c5=function(_c6){return new F(function(){return A(_bU,[[1,new T(function(){return B(_b2(B(_bQ(_b6,_c6))));})]]);});};return [1,B(_9O(_aP,_c5))];}else{return [2];}};return B(_82(B(_82([0,_c3],[0,_bZ])),_bW));});return new F(function(){return _82([0,function(_c7){return (E(_c7)==101)?E(_bV):[2];}],[0,function(_c8){return (E(_c8)==69)?E(_bV):[2];}]);});},_c9=function(_ca){var _cb=function(_cc){return new F(function(){return A(_ca,[[1,_cc]]);});};return function(_cd){return (E(_cd)==46)?[1,B(_9O(_aP,_cb))]:[2];};},_ce=function(_cf){return [0,B(_c9(_cf))];},_cg=function(_ch){var _ci=function(_cj){var _ck=function(_cl){return [1,B(_97(_bT,_aL,function(_cm){return new F(function(){return A(_ch,[[5,[1,_cj,_cl,_cm]]]);});}))];};return [1,B(_97(_ce,_aN,_ck))];};return new F(function(){return _9O(_aP,_ci);});},_cn=function(_co){return [1,B(_cg(_co))];},_cp=function(_cq,_cr,_cs){while(1){var _ct=E(_cs);if(!_ct[0]){return false;}else{if(!B(A(_T,[_cq,_cr,_ct[1]]))){_cs=_ct[2];continue;}else{return true;}}}},_cu=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_cv=function(_cw){return new F(function(){return _cp(_8D,_cw,_cu);});},_cx=false,_cy=true,_cz=function(_cA){var _cB=new T(function(){return B(A(_cA,[_az]));}),_cC=new T(function(){return B(A(_cA,[_ay]));});return function(_cD){switch(E(_cD)){case 79:return E(_cB);case 88:return E(_cC);case 111:return E(_cB);case 120:return E(_cC);default:return [2];}};},_cE=function(_cF){return [0,B(_cz(_cF))];},_cG=function(_cH){return new F(function(){return A(_cH,[_aP]);});},_cI=function(_cJ){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_1g(9,_cJ,_1l));}))));});},_cK=function(_cL){var _cM=E(_cL);if(!_cM[0]){return E(_cM[1]);}else{return new F(function(){return I_toInt(_cM[1]);});}},_cN=function(_cO,_cP){var _cQ=E(_cO);if(!_cQ[0]){var _cR=_cQ[1],_cS=E(_cP);return (_cS[0]==0)?_cR<=_cS[1]:I_compareInt(_cS[1],_cR)>=0;}else{var _cT=_cQ[1],_cU=E(_cP);return (_cU[0]==0)?I_compareInt(_cT,_cU[1])<=0:I_compare(_cT,_cU[1])<=0;}},_cV=function(_cW){return [2];},_cX=function(_cY){var _cZ=E(_cY);if(!_cZ[0]){return E(_cV);}else{var _d0=_cZ[1],_d1=E(_cZ[2]);if(!_d1[0]){return E(_d0);}else{var _d2=new T(function(){return B(_cX(_d1));}),_d3=function(_d4){return new F(function(){return _82(B(A(_d0,[_d4])),new T(function(){return B(A(_d2,[_d4]));}));});};return E(_d3);}}},_d5=function(_d6,_d7){var _d8=function(_d9,_da,_db){var _dc=E(_d9);if(!_dc[0]){return new F(function(){return A(_db,[_d6]);});}else{var _dd=E(_da);if(!_dd[0]){return [2];}else{if(E(_dc[1])!=E(_dd[1])){return [2];}else{var _de=new T(function(){return B(_d8(_dc[2],_dd[2],_db));});return [0,function(_df){return E(_de);}];}}}};return function(_dg){return new F(function(){return _d8(_d6,_dg,_d7);});};},_dh=new T(function(){return B(unCStr("SO"));}),_di=14,_dj=function(_dk){var _dl=new T(function(){return B(A(_dk,[_di]));});return [1,B(_d5(_dh,function(_dm){return E(_dl);}))];},_dn=new T(function(){return B(unCStr("SOH"));}),_do=1,_dp=function(_dq){var _dr=new T(function(){return B(A(_dq,[_do]));});return [1,B(_d5(_dn,function(_ds){return E(_dr);}))];},_dt=function(_du){return [1,B(_97(_dp,_dj,_du))];},_dv=new T(function(){return B(unCStr("NUL"));}),_dw=0,_dx=function(_dy){var _dz=new T(function(){return B(A(_dy,[_dw]));});return [1,B(_d5(_dv,function(_dA){return E(_dz);}))];},_dB=new T(function(){return B(unCStr("STX"));}),_dC=2,_dD=function(_dE){var _dF=new T(function(){return B(A(_dE,[_dC]));});return [1,B(_d5(_dB,function(_dG){return E(_dF);}))];},_dH=new T(function(){return B(unCStr("ETX"));}),_dI=3,_dJ=function(_dK){var _dL=new T(function(){return B(A(_dK,[_dI]));});return [1,B(_d5(_dH,function(_dM){return E(_dL);}))];},_dN=new T(function(){return B(unCStr("EOT"));}),_dO=4,_dP=function(_dQ){var _dR=new T(function(){return B(A(_dQ,[_dO]));});return [1,B(_d5(_dN,function(_dS){return E(_dR);}))];},_dT=new T(function(){return B(unCStr("ENQ"));}),_dU=5,_dV=function(_dW){var _dX=new T(function(){return B(A(_dW,[_dU]));});return [1,B(_d5(_dT,function(_dY){return E(_dX);}))];},_dZ=new T(function(){return B(unCStr("ACK"));}),_e0=6,_e1=function(_e2){var _e3=new T(function(){return B(A(_e2,[_e0]));});return [1,B(_d5(_dZ,function(_e4){return E(_e3);}))];},_e5=new T(function(){return B(unCStr("BEL"));}),_e6=7,_e7=function(_e8){var _e9=new T(function(){return B(A(_e8,[_e6]));});return [1,B(_d5(_e5,function(_ea){return E(_e9);}))];},_eb=new T(function(){return B(unCStr("BS"));}),_ec=8,_ed=function(_ee){var _ef=new T(function(){return B(A(_ee,[_ec]));});return [1,B(_d5(_eb,function(_eg){return E(_ef);}))];},_eh=new T(function(){return B(unCStr("HT"));}),_ei=9,_ej=function(_ek){var _el=new T(function(){return B(A(_ek,[_ei]));});return [1,B(_d5(_eh,function(_em){return E(_el);}))];},_en=new T(function(){return B(unCStr("LF"));}),_eo=10,_ep=function(_eq){var _er=new T(function(){return B(A(_eq,[_eo]));});return [1,B(_d5(_en,function(_es){return E(_er);}))];},_et=new T(function(){return B(unCStr("VT"));}),_eu=11,_ev=function(_ew){var _ex=new T(function(){return B(A(_ew,[_eu]));});return [1,B(_d5(_et,function(_ey){return E(_ex);}))];},_ez=new T(function(){return B(unCStr("FF"));}),_eA=12,_eB=function(_eC){var _eD=new T(function(){return B(A(_eC,[_eA]));});return [1,B(_d5(_ez,function(_eE){return E(_eD);}))];},_eF=new T(function(){return B(unCStr("CR"));}),_eG=13,_eH=function(_eI){var _eJ=new T(function(){return B(A(_eI,[_eG]));});return [1,B(_d5(_eF,function(_eK){return E(_eJ);}))];},_eL=new T(function(){return B(unCStr("SI"));}),_eM=15,_eN=function(_eO){var _eP=new T(function(){return B(A(_eO,[_eM]));});return [1,B(_d5(_eL,function(_eQ){return E(_eP);}))];},_eR=new T(function(){return B(unCStr("DLE"));}),_eS=16,_eT=function(_eU){var _eV=new T(function(){return B(A(_eU,[_eS]));});return [1,B(_d5(_eR,function(_eW){return E(_eV);}))];},_eX=new T(function(){return B(unCStr("DC1"));}),_eY=17,_eZ=function(_f0){var _f1=new T(function(){return B(A(_f0,[_eY]));});return [1,B(_d5(_eX,function(_f2){return E(_f1);}))];},_f3=new T(function(){return B(unCStr("DC2"));}),_f4=18,_f5=function(_f6){var _f7=new T(function(){return B(A(_f6,[_f4]));});return [1,B(_d5(_f3,function(_f8){return E(_f7);}))];},_f9=new T(function(){return B(unCStr("DC3"));}),_fa=19,_fb=function(_fc){var _fd=new T(function(){return B(A(_fc,[_fa]));});return [1,B(_d5(_f9,function(_fe){return E(_fd);}))];},_ff=new T(function(){return B(unCStr("DC4"));}),_fg=20,_fh=function(_fi){var _fj=new T(function(){return B(A(_fi,[_fg]));});return [1,B(_d5(_ff,function(_fk){return E(_fj);}))];},_fl=new T(function(){return B(unCStr("NAK"));}),_fm=21,_fn=function(_fo){var _fp=new T(function(){return B(A(_fo,[_fm]));});return [1,B(_d5(_fl,function(_fq){return E(_fp);}))];},_fr=new T(function(){return B(unCStr("SYN"));}),_fs=22,_ft=function(_fu){var _fv=new T(function(){return B(A(_fu,[_fs]));});return [1,B(_d5(_fr,function(_fw){return E(_fv);}))];},_fx=new T(function(){return B(unCStr("ETB"));}),_fy=23,_fz=function(_fA){var _fB=new T(function(){return B(A(_fA,[_fy]));});return [1,B(_d5(_fx,function(_fC){return E(_fB);}))];},_fD=new T(function(){return B(unCStr("CAN"));}),_fE=24,_fF=function(_fG){var _fH=new T(function(){return B(A(_fG,[_fE]));});return [1,B(_d5(_fD,function(_fI){return E(_fH);}))];},_fJ=new T(function(){return B(unCStr("EM"));}),_fK=25,_fL=function(_fM){var _fN=new T(function(){return B(A(_fM,[_fK]));});return [1,B(_d5(_fJ,function(_fO){return E(_fN);}))];},_fP=new T(function(){return B(unCStr("SUB"));}),_fQ=26,_fR=function(_fS){var _fT=new T(function(){return B(A(_fS,[_fQ]));});return [1,B(_d5(_fP,function(_fU){return E(_fT);}))];},_fV=new T(function(){return B(unCStr("ESC"));}),_fW=27,_fX=function(_fY){var _fZ=new T(function(){return B(A(_fY,[_fW]));});return [1,B(_d5(_fV,function(_g0){return E(_fZ);}))];},_g1=new T(function(){return B(unCStr("FS"));}),_g2=28,_g3=function(_g4){var _g5=new T(function(){return B(A(_g4,[_g2]));});return [1,B(_d5(_g1,function(_g6){return E(_g5);}))];},_g7=new T(function(){return B(unCStr("GS"));}),_g8=29,_g9=function(_ga){var _gb=new T(function(){return B(A(_ga,[_g8]));});return [1,B(_d5(_g7,function(_gc){return E(_gb);}))];},_gd=new T(function(){return B(unCStr("RS"));}),_ge=30,_gf=function(_gg){var _gh=new T(function(){return B(A(_gg,[_ge]));});return [1,B(_d5(_gd,function(_gi){return E(_gh);}))];},_gj=new T(function(){return B(unCStr("US"));}),_gk=31,_gl=function(_gm){var _gn=new T(function(){return B(A(_gm,[_gk]));});return [1,B(_d5(_gj,function(_go){return E(_gn);}))];},_gp=new T(function(){return B(unCStr("SP"));}),_gq=32,_gr=function(_gs){var _gt=new T(function(){return B(A(_gs,[_gq]));});return [1,B(_d5(_gp,function(_gu){return E(_gt);}))];},_gv=new T(function(){return B(unCStr("DEL"));}),_gw=127,_gx=function(_gy){var _gz=new T(function(){return B(A(_gy,[_gw]));});return [1,B(_d5(_gv,function(_gA){return E(_gz);}))];},_gB=[1,_gx,_1l],_gC=[1,_gr,_gB],_gD=[1,_gl,_gC],_gE=[1,_gf,_gD],_gF=[1,_g9,_gE],_gG=[1,_g3,_gF],_gH=[1,_fX,_gG],_gI=[1,_fR,_gH],_gJ=[1,_fL,_gI],_gK=[1,_fF,_gJ],_gL=[1,_fz,_gK],_gM=[1,_ft,_gL],_gN=[1,_fn,_gM],_gO=[1,_fh,_gN],_gP=[1,_fb,_gO],_gQ=[1,_f5,_gP],_gR=[1,_eZ,_gQ],_gS=[1,_eT,_gR],_gT=[1,_eN,_gS],_gU=[1,_eH,_gT],_gV=[1,_eB,_gU],_gW=[1,_ev,_gV],_gX=[1,_ep,_gW],_gY=[1,_ej,_gX],_gZ=[1,_ed,_gY],_h0=[1,_e7,_gZ],_h1=[1,_e1,_h0],_h2=[1,_dV,_h1],_h3=[1,_dP,_h2],_h4=[1,_dJ,_h3],_h5=[1,_dD,_h4],_h6=[1,_dx,_h5],_h7=[1,_dt,_h6],_h8=new T(function(){return B(_cX(_h7));}),_h9=34,_ha=[0,1114111],_hb=92,_hc=39,_hd=function(_he){var _hf=new T(function(){return B(A(_he,[_e6]));}),_hg=new T(function(){return B(A(_he,[_ec]));}),_hh=new T(function(){return B(A(_he,[_ei]));}),_hi=new T(function(){return B(A(_he,[_eo]));}),_hj=new T(function(){return B(A(_he,[_eu]));}),_hk=new T(function(){return B(A(_he,[_eA]));}),_hl=new T(function(){return B(A(_he,[_eG]));}),_hm=new T(function(){return B(A(_he,[_hb]));}),_hn=new T(function(){return B(A(_he,[_hc]));}),_ho=new T(function(){return B(A(_he,[_h9]));}),_hp=new T(function(){var _hq=function(_hr){var _hs=new T(function(){return B(_bg(E(_hr)));}),_ht=function(_hu){var _hv=B(_bQ(_hs,_hu));if(!B(_cN(_hv,_ha))){return [2];}else{return new F(function(){return A(_he,[new T(function(){var _hw=B(_cK(_hv));if(_hw>>>0>1114111){return B(_cI(_hw));}else{return _hw;}})]);});}};return [1,B(_9O(_hr,_ht))];},_hx=new T(function(){var _hy=new T(function(){return B(A(_he,[_gk]));}),_hz=new T(function(){return B(A(_he,[_ge]));}),_hA=new T(function(){return B(A(_he,[_g8]));}),_hB=new T(function(){return B(A(_he,[_g2]));}),_hC=new T(function(){return B(A(_he,[_fW]));}),_hD=new T(function(){return B(A(_he,[_fQ]));}),_hE=new T(function(){return B(A(_he,[_fK]));}),_hF=new T(function(){return B(A(_he,[_fE]));}),_hG=new T(function(){return B(A(_he,[_fy]));}),_hH=new T(function(){return B(A(_he,[_fs]));}),_hI=new T(function(){return B(A(_he,[_fm]));}),_hJ=new T(function(){return B(A(_he,[_fg]));}),_hK=new T(function(){return B(A(_he,[_fa]));}),_hL=new T(function(){return B(A(_he,[_f4]));}),_hM=new T(function(){return B(A(_he,[_eY]));}),_hN=new T(function(){return B(A(_he,[_eS]));}),_hO=new T(function(){return B(A(_he,[_eM]));}),_hP=new T(function(){return B(A(_he,[_di]));}),_hQ=new T(function(){return B(A(_he,[_e0]));}),_hR=new T(function(){return B(A(_he,[_dU]));}),_hS=new T(function(){return B(A(_he,[_dO]));}),_hT=new T(function(){return B(A(_he,[_dI]));}),_hU=new T(function(){return B(A(_he,[_dC]));}),_hV=new T(function(){return B(A(_he,[_do]));}),_hW=new T(function(){return B(A(_he,[_dw]));}),_hX=function(_hY){switch(E(_hY)){case 64:return E(_hW);case 65:return E(_hV);case 66:return E(_hU);case 67:return E(_hT);case 68:return E(_hS);case 69:return E(_hR);case 70:return E(_hQ);case 71:return E(_hf);case 72:return E(_hg);case 73:return E(_hh);case 74:return E(_hi);case 75:return E(_hj);case 76:return E(_hk);case 77:return E(_hl);case 78:return E(_hP);case 79:return E(_hO);case 80:return E(_hN);case 81:return E(_hM);case 82:return E(_hL);case 83:return E(_hK);case 84:return E(_hJ);case 85:return E(_hI);case 86:return E(_hH);case 87:return E(_hG);case 88:return E(_hF);case 89:return E(_hE);case 90:return E(_hD);case 91:return E(_hC);case 92:return E(_hB);case 93:return E(_hA);case 94:return E(_hz);case 95:return E(_hy);default:return [2];}};return B(_82([0,function(_hZ){return (E(_hZ)==94)?[0,_hX]:[2];}],new T(function(){return B(A(_h8,[_he]));})));});return B(_82([1,B(_97(_cE,_cG,_hq))],_hx));});return new F(function(){return _82([0,function(_i0){switch(E(_i0)){case 34:return E(_ho);case 39:return E(_hn);case 92:return E(_hm);case 97:return E(_hf);case 98:return E(_hg);case 102:return E(_hk);case 110:return E(_hi);case 114:return E(_hl);case 116:return E(_hh);case 118:return E(_hj);default:return [2];}}],_hp);});},_i1=function(_i2){return new F(function(){return A(_i2,[_a]);});},_i3=function(_i4){var _i5=E(_i4);if(!_i5[0]){return E(_i1);}else{var _i6=E(_i5[1]),_i7=_i6>>>0,_i8=new T(function(){return B(_i3(_i5[2]));});if(_i7>887){var _i9=u_iswspace(_i6);if(!E(_i9)){return E(_i1);}else{var _ia=function(_ib){var _ic=new T(function(){return B(A(_i8,[_ib]));});return [0,function(_id){return E(_ic);}];};return E(_ia);}}else{var _ie=E(_i7);if(_ie==32){var _if=function(_ig){var _ih=new T(function(){return B(A(_i8,[_ig]));});return [0,function(_ii){return E(_ih);}];};return E(_if);}else{if(_ie-9>>>0>4){if(E(_ie)==160){var _ij=function(_ik){var _il=new T(function(){return B(A(_i8,[_ik]));});return [0,function(_im){return E(_il);}];};return E(_ij);}else{return E(_i1);}}else{var _in=function(_io){var _ip=new T(function(){return B(A(_i8,[_io]));});return [0,function(_iq){return E(_ip);}];};return E(_in);}}}}},_ir=function(_is){var _it=new T(function(){return B(_ir(_is));}),_iu=function(_iv){return (E(_iv)==92)?E(_it):[2];},_iw=function(_ix){return [0,_iu];},_iy=[1,function(_iz){return new F(function(){return A(_i3,[_iz,_iw]);});}],_iA=new T(function(){return B(_hd(function(_iB){return new F(function(){return A(_is,[[0,_iB,_cy]]);});}));}),_iC=function(_iD){var _iE=E(_iD);if(_iE==38){return E(_it);}else{var _iF=_iE>>>0;if(_iF>887){var _iG=u_iswspace(_iE);return (E(_iG)==0)?[2]:E(_iy);}else{var _iH=E(_iF);return (_iH==32)?E(_iy):(_iH-9>>>0>4)?(E(_iH)==160)?E(_iy):[2]:E(_iy);}}};return new F(function(){return _82([0,function(_iI){return (E(_iI)==92)?[0,_iC]:[2];}],[0,function(_iJ){var _iK=E(_iJ);if(E(_iK)==92){return E(_iA);}else{return new F(function(){return A(_is,[[0,_iK,_cx]]);});}}]);});},_iL=function(_iM,_iN){var _iO=new T(function(){return B(A(_iN,[[1,new T(function(){return B(A(_iM,[_1l]));})]]));}),_iP=function(_iQ){var _iR=E(_iQ),_iS=E(_iR[1]);if(E(_iS)==34){if(!E(_iR[2])){return E(_iO);}else{return new F(function(){return _iL(function(_iT){return new F(function(){return A(_iM,[[1,_iS,_iT]]);});},_iN);});}}else{return new F(function(){return _iL(function(_iU){return new F(function(){return A(_iM,[[1,_iS,_iU]]);});},_iN);});}};return new F(function(){return _ir(_iP);});},_iV=new T(function(){return B(unCStr("_\'"));}),_iW=function(_iX){var _iY=u_iswalnum(_iX);if(!E(_iY)){return new F(function(){return _cp(_8D,_iX,_iV);});}else{return true;}},_iZ=function(_j0){return new F(function(){return _iW(E(_j0));});},_j1=new T(function(){return B(unCStr(",;()[]{}`"));}),_j2=new T(function(){return B(unCStr("=>"));}),_j3=[1,_j2,_1l],_j4=new T(function(){return B(unCStr("~"));}),_j5=[1,_j4,_j3],_j6=new T(function(){return B(unCStr("@"));}),_j7=[1,_j6,_j5],_j8=new T(function(){return B(unCStr("->"));}),_j9=[1,_j8,_j7],_ja=new T(function(){return B(unCStr("<-"));}),_jb=[1,_ja,_j9],_jc=new T(function(){return B(unCStr("|"));}),_jd=[1,_jc,_jb],_je=new T(function(){return B(unCStr("\\"));}),_jf=[1,_je,_jd],_jg=new T(function(){return B(unCStr("="));}),_jh=[1,_jg,_jf],_ji=new T(function(){return B(unCStr("::"));}),_jj=[1,_ji,_jh],_jk=new T(function(){return B(unCStr(".."));}),_jl=[1,_jk,_jj],_jm=function(_jn){var _jo=new T(function(){return B(A(_jn,[_9L]));}),_jp=new T(function(){var _jq=new T(function(){var _jr=function(_js){var _jt=new T(function(){return B(A(_jn,[[0,_js]]));});return [0,function(_ju){return (E(_ju)==39)?E(_jt):[2];}];};return B(_hd(_jr));}),_jv=function(_jw){var _jx=E(_jw);switch(E(_jx)){case 39:return [2];case 92:return E(_jq);default:var _jy=new T(function(){return B(A(_jn,[[0,_jx]]));});return [0,function(_jz){return (E(_jz)==39)?E(_jy):[2];}];}},_jA=new T(function(){var _jB=new T(function(){return B(_iL(_Q,_jn));}),_jC=new T(function(){var _jD=new T(function(){var _jE=new T(function(){var _jF=function(_jG){var _jH=E(_jG),_jI=u_iswalpha(_jH);return (E(_jI)==0)?(E(_jH)==95)?[1,B(_9x(_iZ,function(_jJ){return new F(function(){return A(_jn,[[3,[1,_jH,_jJ]]]);});}))]:[2]:[1,B(_9x(_iZ,function(_jK){return new F(function(){return A(_jn,[[3,[1,_jH,_jK]]]);});}))];};return B(_82([0,_jF],new T(function(){return [1,B(_97(_aJ,_cn,_jn))];})));}),_jL=function(_jM){return (!B(_cp(_8D,_jM,_cu)))?[2]:[1,B(_9x(_cv,function(_jN){var _jO=[1,_jM,_jN];if(!B(_cp(_8M,_jO,_jl))){return new F(function(){return A(_jn,[[4,_jO]]);});}else{return new F(function(){return A(_jn,[[2,_jO]]);});}}))];};return B(_82([0,_jL],_jE));});return B(_82([0,function(_jP){if(!B(_cp(_8D,_jP,_j1))){return [2];}else{return new F(function(){return A(_jn,[[2,[1,_jP,_1l]]]);});}}],_jD));});return B(_82([0,function(_jQ){return (E(_jQ)==34)?E(_jB):[2];}],_jC));});return B(_82([0,function(_jR){return (E(_jR)==39)?[0,_jv]:[2];}],_jA));});return new F(function(){return _82([1,function(_jS){return (E(_jS)[0]==0)?E(_jo):[2];}],_jp);});},_jT=0,_jU=function(_jV,_jW){var _jX=new T(function(){var _jY=new T(function(){var _jZ=function(_k0){var _k1=new T(function(){var _k2=new T(function(){return B(A(_jW,[_k0]));});return B(_jm(function(_k3){var _k4=E(_k3);return (_k4[0]==2)?(!B(_2b(_k4[1],_8w)))?[2]:E(_k2):[2];}));}),_k5=function(_k6){return E(_k1);};return [1,function(_k7){return new F(function(){return A(_i3,[_k7,_k5]);});}];};return B(A(_jV,[_jT,_jZ]));});return B(_jm(function(_k8){var _k9=E(_k8);return (_k9[0]==2)?(!B(_2b(_k9[1],_8v)))?[2]:E(_jY):[2];}));}),_ka=function(_kb){return E(_jX);};return function(_kc){return new F(function(){return A(_i3,[_kc,_ka]);});};},_kd=function(_ke,_kf){var _kg=function(_kh){var _ki=new T(function(){return B(A(_ke,[_kh]));}),_kj=function(_kk){return new F(function(){return _82(B(A(_ki,[_kk])),new T(function(){return [1,B(_jU(_kg,_kk))];}));});};return E(_kj);},_kl=new T(function(){return B(A(_ke,[_kf]));}),_km=function(_kn){return new F(function(){return _82(B(A(_kl,[_kn])),new T(function(){return [1,B(_jU(_kg,_kn))];}));});};return E(_km);},_ko=function(_kp,_kq){var _kr=function(_ks,_kt){var _ku=function(_kv){return new F(function(){return A(_kt,[new T(function(){return  -E(_kv);})]);});},_kw=new T(function(){return B(_jm(function(_kx){return new F(function(){return A(_kp,[_kx,_ks,_ku]);});}));}),_ky=function(_kz){return E(_kw);},_kA=function(_kB){return new F(function(){return A(_i3,[_kB,_ky]);});},_kC=new T(function(){return B(_jm(function(_kD){var _kE=E(_kD);if(_kE[0]==4){var _kF=E(_kE[1]);if(!_kF[0]){return new F(function(){return A(_kp,[_kE,_ks,_kt]);});}else{if(E(_kF[1])==45){if(!E(_kF[2])[0]){return [1,_kA];}else{return new F(function(){return A(_kp,[_kE,_ks,_kt]);});}}else{return new F(function(){return A(_kp,[_kE,_ks,_kt]);});}}}else{return new F(function(){return A(_kp,[_kE,_ks,_kt]);});}}));}),_kG=function(_kH){return E(_kC);};return [1,function(_kI){return new F(function(){return A(_i3,[_kI,_kG]);});}];};return new F(function(){return _kd(_kr,_kq);});},_kJ=new T(function(){return 1/0;}),_kK=function(_kL,_kM){return new F(function(){return A(_kM,[_kJ]);});},_kN=new T(function(){return 0/0;}),_kO=function(_kP,_kQ){return new F(function(){return A(_kQ,[_kN]);});},_kR=new T(function(){return B(unCStr("NaN"));}),_kS=new T(function(){return B(unCStr("Infinity"));}),_kT=1024,_kU=-1021,_kV=new T(function(){return B(unCStr("GHC.Exception"));}),_kW=new T(function(){return B(unCStr("base"));}),_kX=new T(function(){return B(unCStr("ArithException"));}),_kY=new T(function(){var _kZ=hs_wordToWord64(4194982440),_l0=hs_wordToWord64(3110813675);return [0,_kZ,_l0,[0,_kZ,_l0,_kW,_kV,_kX],_1l,_1l];}),_l1=function(_l2){return E(_kY);},_l3=function(_l4){var _l5=E(_l4);return new F(function(){return _5g(B(_5e(_l5[1])),_l1,_l5[2]);});},_l6=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_l7=new T(function(){return B(unCStr("denormal"));}),_l8=new T(function(){return B(unCStr("divide by zero"));}),_l9=new T(function(){return B(unCStr("loss of precision"));}),_la=new T(function(){return B(unCStr("arithmetic underflow"));}),_lb=new T(function(){return B(unCStr("arithmetic overflow"));}),_lc=function(_ld,_le){switch(E(_ld)){case 0:return new F(function(){return _16(_lb,_le);});break;case 1:return new F(function(){return _16(_la,_le);});break;case 2:return new F(function(){return _16(_l9,_le);});break;case 3:return new F(function(){return _16(_l8,_le);});break;case 4:return new F(function(){return _16(_l7,_le);});break;default:return new F(function(){return _16(_l6,_le);});}},_lf=function(_lg){return new F(function(){return _lc(_lg,_1l);});},_lh=function(_li,_lj,_lk){return new F(function(){return _lc(_lj,_lk);});},_ll=function(_lm,_ln){return new F(function(){return _6r(_lc,_lm,_ln);});},_lo=[0,_lh,_lf,_ll],_lp=new T(function(){return [0,_l1,_lo,_lq,_l3,_lf];}),_lq=function(_7s){return [0,_lp,_7s];},_lr=3,_ls=new T(function(){return B(_lq(_lr));}),_lt=new T(function(){return die(_ls);}),_lu=function(_lv,_lw){var _lx=E(_lv);if(!_lx[0]){var _ly=_lx[1],_lz=E(_lw);return (_lz[0]==0)?_ly==_lz[1]:(I_compareInt(_lz[1],_ly)==0)?true:false;}else{var _lA=_lx[1],_lB=E(_lw);return (_lB[0]==0)?(I_compareInt(_lA,_lB[1])==0)?true:false:(I_compare(_lA,_lB[1])==0)?true:false;}},_lC=[0,0],_lD=function(_lE,_lF){while(1){var _lG=E(_lE);if(!_lG[0]){var _lH=E(_lG[1]);if(_lH==(-2147483648)){_lE=[1,I_fromInt(-2147483648)];continue;}else{var _lI=E(_lF);if(!_lI[0]){return [0,_lH%_lI[1]];}else{_lE=[1,I_fromInt(_lH)];_lF=_lI;continue;}}}else{var _lJ=_lG[1],_lK=E(_lF);return (_lK[0]==0)?[1,I_rem(_lJ,I_fromInt(_lK[1]))]:[1,I_rem(_lJ,_lK[1])];}}},_lL=function(_lM,_lN){if(!B(_lu(_lN,_lC))){return new F(function(){return _lD(_lM,_lN);});}else{return E(_lt);}},_lO=function(_lP,_lQ){while(1){if(!B(_lu(_lQ,_lC))){var _lR=_lQ,_lS=B(_lL(_lP,_lQ));_lP=_lR;_lQ=_lS;continue;}else{return E(_lP);}}},_lT=function(_lU){var _lV=E(_lU);if(!_lV[0]){var _lW=E(_lV[1]);return (_lW==(-2147483648))?E(_b1):(_lW<0)?[0, -_lW]:E(_lV);}else{var _lX=_lV[1];return (I_compareInt(_lX,0)>=0)?E(_lV):[1,I_negate(_lX)];}},_lY=function(_lZ,_m0){while(1){var _m1=E(_lZ);if(!_m1[0]){var _m2=E(_m1[1]);if(_m2==(-2147483648)){_lZ=[1,I_fromInt(-2147483648)];continue;}else{var _m3=E(_m0);if(!_m3[0]){return [0,quot(_m2,_m3[1])];}else{_lZ=[1,I_fromInt(_m2)];_m0=_m3;continue;}}}else{var _m4=_m1[1],_m5=E(_m0);return (_m5[0]==0)?[0,I_toInt(I_quot(_m4,I_fromInt(_m5[1])))]:[1,I_quot(_m4,_m5[1])];}}},_m6=5,_m7=new T(function(){return B(_lq(_m6));}),_m8=new T(function(){return die(_m7);}),_m9=function(_ma,_mb){if(!B(_lu(_mb,_lC))){var _mc=B(_lO(B(_lT(_ma)),B(_lT(_mb))));return (!B(_lu(_mc,_lC)))?[0,B(_lY(_ma,_mc)),B(_lY(_mb,_mc))]:E(_lt);}else{return E(_m8);}},_md=[0,1],_me=new T(function(){return B(unCStr("Negative exponent"));}),_mf=new T(function(){return B(err(_me));}),_mg=[0,2],_mh=new T(function(){return B(_lu(_mg,_lC));}),_mi=function(_mj,_mk){while(1){var _ml=E(_mj);if(!_ml[0]){var _mm=_ml[1],_mn=E(_mk);if(!_mn[0]){var _mo=_mn[1],_mp=subC(_mm,_mo);if(!E(_mp[2])){return [0,_mp[1]];}else{_mj=[1,I_fromInt(_mm)];_mk=[1,I_fromInt(_mo)];continue;}}else{_mj=[1,I_fromInt(_mm)];_mk=_mn;continue;}}else{var _mq=E(_mk);if(!_mq[0]){_mj=_ml;_mk=[1,I_fromInt(_mq[1])];continue;}else{return [1,I_sub(_ml[1],_mq[1])];}}}},_mr=function(_ms,_mt,_mu){while(1){if(!E(_mh)){if(!B(_lu(B(_lD(_mt,_mg)),_lC))){if(!B(_lu(_mt,_md))){var _mv=B(_bm(_ms,_ms)),_mw=B(_lY(B(_mi(_mt,_md)),_mg)),_mx=B(_bm(_ms,_mu));_ms=_mv;_mt=_mw;_mu=_mx;continue;}else{return new F(function(){return _bm(_ms,_mu);});}}else{var _mv=B(_bm(_ms,_ms)),_mw=B(_lY(_mt,_mg));_ms=_mv;_mt=_mw;continue;}}else{return E(_lt);}}},_my=function(_mz,_mA){while(1){if(!E(_mh)){if(!B(_lu(B(_lD(_mA,_mg)),_lC))){if(!B(_lu(_mA,_md))){return new F(function(){return _mr(B(_bm(_mz,_mz)),B(_lY(B(_mi(_mA,_md)),_mg)),_mz);});}else{return E(_mz);}}else{var _mB=B(_bm(_mz,_mz)),_mC=B(_lY(_mA,_mg));_mz=_mB;_mA=_mC;continue;}}else{return E(_lt);}}},_mD=function(_mE,_mF){var _mG=E(_mE);if(!_mG[0]){var _mH=_mG[1],_mI=E(_mF);return (_mI[0]==0)?_mH<_mI[1]:I_compareInt(_mI[1],_mH)>0;}else{var _mJ=_mG[1],_mK=E(_mF);return (_mK[0]==0)?I_compareInt(_mJ,_mK[1])<0:I_compare(_mJ,_mK[1])<0;}},_mL=function(_mM,_mN){if(!B(_mD(_mN,_lC))){if(!B(_lu(_mN,_lC))){return new F(function(){return _my(_mM,_mN);});}else{return E(_md);}}else{return E(_mf);}},_mO=[0,1],_mP=[0,0],_mQ=[0,-1],_mR=function(_mS){var _mT=E(_mS);if(!_mT[0]){var _mU=_mT[1];return (_mU>=0)?(E(_mU)==0)?E(_mP):E(_aQ):E(_mQ);}else{var _mV=I_compareInt(_mT[1],0);return (_mV<=0)?(E(_mV)==0)?E(_mP):E(_mQ):E(_aQ);}},_mW=function(_mX,_mY,_mZ){while(1){var _n0=E(_mZ);if(!_n0[0]){if(!B(_mD(_mX,_bz))){return [0,B(_bm(_mY,B(_mL(_b6,_mX)))),_md];}else{var _n1=B(_mL(_b6,B(_b2(_mX))));return new F(function(){return _m9(B(_bm(_mY,B(_mR(_n1)))),B(_lT(_n1)));});}}else{var _n2=B(_mi(_mX,_mO)),_n3=B(_aS(B(_bm(_mY,_b6)),B(_bg(E(_n0[1])))));_mX=_n2;_mY=_n3;_mZ=_n0[2];continue;}}},_n4=function(_n5,_n6){var _n7=E(_n5);if(!_n7[0]){var _n8=_n7[1],_n9=E(_n6);return (_n9[0]==0)?_n8>=_n9[1]:I_compareInt(_n9[1],_n8)<=0;}else{var _na=_n7[1],_nb=E(_n6);return (_nb[0]==0)?I_compareInt(_na,_nb[1])>=0:I_compare(_na,_nb[1])>=0;}},_nc=function(_nd){var _ne=E(_nd);if(!_ne[0]){var _nf=_ne[2];return new F(function(){return _m9(B(_bm(B(_bA(new T(function(){return B(_bg(E(_ne[1])));}),new T(function(){return B(_b7(_nf,0));},1),B(_bc(_bi,_nf)))),_mO)),_mO);});}else{var _ng=_ne[1],_nh=_ne[3],_ni=E(_ne[2]);if(!_ni[0]){var _nj=E(_nh);if(!_nj[0]){return new F(function(){return _m9(B(_bm(B(_bQ(_b6,_ng)),_mO)),_mO);});}else{var _nk=_nj[1];if(!B(_n4(_nk,_bz))){var _nl=B(_mL(_b6,B(_b2(_nk))));return new F(function(){return _m9(B(_bm(B(_bQ(_b6,_ng)),B(_mR(_nl)))),B(_lT(_nl)));});}else{return new F(function(){return _m9(B(_bm(B(_bm(B(_bQ(_b6,_ng)),B(_mL(_b6,_nk)))),_mO)),_mO);});}}}else{var _nm=_ni[1],_nn=E(_nh);if(!_nn[0]){return new F(function(){return _mW(_bz,B(_bQ(_b6,_ng)),_nm);});}else{return new F(function(){return _mW(_nn[1],B(_bQ(_b6,_ng)),_nm);});}}}},_no=function(_np,_nq){while(1){var _nr=E(_nq);if(!_nr[0]){return [0];}else{if(!B(A(_np,[_nr[1]]))){return E(_nr);}else{_nq=_nr[2];continue;}}}},_ns=function(_nt,_nu){var _nv=E(_nt);if(!_nv[0]){var _nw=_nv[1],_nx=E(_nu);return (_nx[0]==0)?_nw>_nx[1]:I_compareInt(_nx[1],_nw)<0;}else{var _ny=_nv[1],_nz=E(_nu);return (_nz[0]==0)?I_compareInt(_ny,_nz[1])>0:I_compare(_ny,_nz[1])>0;}},_nA=0,_nB=function(_nC,_nD){return E(_nC)==E(_nD);},_nE=function(_nF){return new F(function(){return _nB(_nA,_nF);});},_nG=[0,E(_bz),E(_md)],_nH=[1,_nG],_nI=[0,-2147483648],_nJ=[0,2147483647],_nK=function(_nL,_nM,_nN){var _nO=E(_nN);if(!_nO[0]){return [1,new T(function(){var _nP=B(_nc(_nO));return [0,E(_nP[1]),E(_nP[2])];})];}else{var _nQ=E(_nO[3]);if(!_nQ[0]){return [1,new T(function(){var _nR=B(_nc(_nO));return [0,E(_nR[1]),E(_nR[2])];})];}else{var _nS=_nQ[1];if(!B(_ns(_nS,_nJ))){if(!B(_mD(_nS,_nI))){var _nT=function(_nU){var _nV=_nU+B(_cK(_nS))|0;return (_nV<=(E(_nM)+3|0))?(_nV>=(E(_nL)-3|0))?[1,new T(function(){var _nW=B(_nc(_nO));return [0,E(_nW[1]),E(_nW[2])];})]:E(_nH):[0];},_nX=B(_no(_nE,_nO[1]));if(!_nX[0]){var _nY=E(_nO[2]);if(!_nY[0]){return E(_nH);}else{var _nZ=B(_7t(_nE,_nY[1]));if(!E(_nZ[2])[0]){return E(_nH);}else{return new F(function(){return _nT( -B(_b7(_nZ[1],0)));});}}}else{return new F(function(){return _nT(B(_b7(_nX,0)));});}}else{return [0];}}else{return [0];}}}},_o0=function(_o1,_o2){return [2];},_o3=[0,1],_o4=function(_o5,_o6){var _o7=E(_o5);if(!_o7[0]){var _o8=_o7[1],_o9=E(_o6);if(!_o9[0]){var _oa=_o9[1];return (_o8!=_oa)?(_o8>_oa)?2:0:1;}else{var _ob=I_compareInt(_o9[1],_o8);return (_ob<=0)?(_ob>=0)?1:2:0;}}else{var _oc=_o7[1],_od=E(_o6);if(!_od[0]){var _oe=I_compareInt(_oc,_od[1]);return (_oe>=0)?(_oe<=0)?1:2:0;}else{var _of=I_compare(_oc,_od[1]);return (_of>=0)?(_of<=0)?1:2:0;}}},_og=function(_oh,_oi){var _oj=E(_oh);return (_oj[0]==0)?_oj[1]*Math.pow(2,_oi):I_toNumber(_oj[1])*Math.pow(2,_oi);},_ok=function(_ol,_om){while(1){var _on=E(_ol);if(!_on[0]){var _oo=E(_on[1]);if(_oo==(-2147483648)){_ol=[1,I_fromInt(-2147483648)];continue;}else{var _op=E(_om);if(!_op[0]){var _oq=_op[1];return [0,[0,quot(_oo,_oq)],[0,_oo%_oq]];}else{_ol=[1,I_fromInt(_oo)];_om=_op;continue;}}}else{var _or=E(_om);if(!_or[0]){_ol=_on;_om=[1,I_fromInt(_or[1])];continue;}else{var _os=I_quotRem(_on[1],_or[1]);return [0,[1,_os[1]],[1,_os[2]]];}}}},_ot=[0,0],_ou=function(_ov,_ow){while(1){var _ox=E(_ov);if(!_ox[0]){_ov=[1,I_fromInt(_ox[1])];continue;}else{return [1,I_shiftLeft(_ox[1],_ow)];}}},_oy=function(_oz,_oA,_oB){if(!B(_lu(_oB,_ot))){var _oC=B(_ok(_oA,_oB)),_oD=_oC[1];switch(B(_o4(B(_ou(_oC[2],1)),_oB))){case 0:return new F(function(){return _og(_oD,_oz);});break;case 1:if(!(B(_cK(_oD))&1)){return new F(function(){return _og(_oD,_oz);});}else{return new F(function(){return _og(B(_aS(_oD,_o3)),_oz);});}break;default:return new F(function(){return _og(B(_aS(_oD,_o3)),_oz);});}}else{return E(_lt);}},_oE=function(_oF){var _oG=_aQ,_oH=0;while(1){if(!B(_mD(_oG,_oF))){if(!B(_ns(_oG,_oF))){if(!B(_lu(_oG,_oF))){return new F(function(){return _7P("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_oH);}}else{return _oH-1|0;}}else{var _oI=B(_ou(_oG,1)),_oJ=_oH+1|0;_oG=_oI;_oH=_oJ;continue;}}},_oK=function(_oL){var _oM=E(_oL);if(!_oM[0]){var _oN=_oM[1]>>>0;if(!_oN){return -1;}else{var _oO=1,_oP=0;while(1){if(_oO>=_oN){if(_oO<=_oN){if(_oO!=_oN){return new F(function(){return _7P("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_oP);}}else{return _oP-1|0;}}else{var _oQ=imul(_oO,2)>>>0,_oR=_oP+1|0;_oO=_oQ;_oP=_oR;continue;}}}}else{return new F(function(){return _oE(_oM);});}},_oS=function(_oT){var _oU=E(_oT);if(!_oU[0]){var _oV=_oU[1]>>>0;if(!_oV){return [0,-1,0];}else{var _oW=function(_oX,_oY){while(1){if(_oX>=_oV){if(_oX<=_oV){if(_oX!=_oV){return new F(function(){return _7P("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_oY);}}else{return _oY-1|0;}}else{var _oZ=imul(_oX,2)>>>0,_p0=_oY+1|0;_oX=_oZ;_oY=_p0;continue;}}};return [0,B(_oW(1,0)),(_oV&_oV-1>>>0)>>>0&4294967295];}}else{var _p1=B(_oK(_oU)),_p2=_p1>>>0;if(!_p2){var _p3=E(_p1);return (_p3==(-2))?[0,-2,0]:[0,_p3,1];}else{var _p4=function(_p5,_p6){while(1){if(_p5>=_p2){if(_p5<=_p2){if(_p5!=_p2){return new F(function(){return _7P("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_p6);}}else{return _p6-1|0;}}else{var _p7=imul(_p5,2)>>>0,_p8=_p6+1|0;_p5=_p7;_p6=_p8;continue;}}},_p9=B(_p4(1,0));return ((_p9+_p9|0)!=_p1)?[0,_p1,1]:[0,_p1,0];}}},_pa=function(_pb,_pc){while(1){var _pd=E(_pb);if(!_pd[0]){var _pe=_pd[1],_pf=E(_pc);if(!_pf[0]){return [0,(_pe>>>0&_pf[1]>>>0)>>>0&4294967295];}else{_pb=[1,I_fromInt(_pe)];_pc=_pf;continue;}}else{var _pg=E(_pc);if(!_pg[0]){_pb=_pd;_pc=[1,I_fromInt(_pg[1])];continue;}else{return [1,I_and(_pd[1],_pg[1])];}}}},_ph=[0,2],_pi=function(_pj,_pk){var _pl=E(_pj);if(!_pl[0]){var _pm=(_pl[1]>>>0&(2<<_pk>>>0)-1>>>0)>>>0,_pn=1<<_pk>>>0;return (_pn<=_pm)?(_pn>=_pm)?1:2:0;}else{var _po=B(_pa(_pl,B(_mi(B(_ou(_ph,_pk)),_aQ)))),_pp=B(_ou(_aQ,_pk));return (!B(_ns(_pp,_po)))?(!B(_mD(_pp,_po)))?1:2:0;}},_pq=function(_pr,_ps){while(1){var _pt=E(_pr);if(!_pt[0]){_pr=[1,I_fromInt(_pt[1])];continue;}else{return [1,I_shiftRight(_pt[1],_ps)];}}},_pu=function(_pv,_pw,_px,_py){var _pz=B(_oS(_py)),_pA=_pz[1];if(!E(_pz[2])){var _pB=B(_oK(_px));if(_pB<((_pA+_pv|0)-1|0)){var _pC=_pA+(_pv-_pw|0)|0;if(_pC>0){if(_pC>_pB){if(_pC<=(_pB+1|0)){if(!E(B(_oS(_px))[2])){return 0;}else{return new F(function(){return _og(_o3,_pv-_pw|0);});}}else{return 0;}}else{var _pD=B(_pq(_px,_pC));switch(B(_pi(_px,_pC-1|0))){case 0:return new F(function(){return _og(_pD,_pv-_pw|0);});break;case 1:if(!(B(_cK(_pD))&1)){return new F(function(){return _og(_pD,_pv-_pw|0);});}else{return new F(function(){return _og(B(_aS(_pD,_o3)),_pv-_pw|0);});}break;default:return new F(function(){return _og(B(_aS(_pD,_o3)),_pv-_pw|0);});}}}else{return new F(function(){return _og(_px,(_pv-_pw|0)-_pC|0);});}}else{if(_pB>=_pw){var _pE=B(_pq(_px,(_pB+1|0)-_pw|0));switch(B(_pi(_px,_pB-_pw|0))){case 0:return new F(function(){return _og(_pE,((_pB-_pA|0)+1|0)-_pw|0);});break;case 2:return new F(function(){return _og(B(_aS(_pE,_o3)),((_pB-_pA|0)+1|0)-_pw|0);});break;default:if(!(B(_cK(_pE))&1)){return new F(function(){return _og(_pE,((_pB-_pA|0)+1|0)-_pw|0);});}else{return new F(function(){return _og(B(_aS(_pE,_o3)),((_pB-_pA|0)+1|0)-_pw|0);});}}}else{return new F(function(){return _og(_px, -_pA);});}}}else{var _pF=B(_oK(_px))-_pA|0,_pG=function(_pH){var _pI=function(_pJ,_pK){if(!B(_cN(B(_ou(_pK,_pw)),_pJ))){return new F(function(){return _oy(_pH-_pw|0,_pJ,_pK);});}else{return new F(function(){return _oy((_pH-_pw|0)+1|0,_pJ,B(_ou(_pK,1)));});}};if(_pH>=_pw){if(_pH!=_pw){return new F(function(){return _pI(_px,new T(function(){return B(_ou(_py,_pH-_pw|0));}));});}else{return new F(function(){return _pI(_px,_py);});}}else{return new F(function(){return _pI(new T(function(){return B(_ou(_px,_pw-_pH|0));}),_py);});}};if(_pv>_pF){return new F(function(){return _pG(_pv);});}else{return new F(function(){return _pG(_pF);});}}},_pL=new T(function(){return 0/0;}),_pM=new T(function(){return -1/0;}),_pN=new T(function(){return 1/0;}),_pO=0,_pP=function(_pQ,_pR){if(!B(_lu(_pR,_ot))){if(!B(_lu(_pQ,_ot))){if(!B(_mD(_pQ,_ot))){return new F(function(){return _pu(-1021,53,_pQ,_pR);});}else{return  -B(_pu(-1021,53,B(_b2(_pQ)),_pR));}}else{return E(_pO);}}else{return (!B(_lu(_pQ,_ot)))?(!B(_mD(_pQ,_ot)))?E(_pN):E(_pM):E(_pL);}},_pS=function(_pT){var _pU=E(_pT);switch(_pU[0]){case 3:var _pV=_pU[1];return (!B(_2b(_pV,_kS)))?(!B(_2b(_pV,_kR)))?E(_o0):E(_kO):E(_kK);case 5:var _pW=B(_nK(_kU,_kT,_pU[1]));if(!_pW[0]){return E(_kK);}else{var _pX=new T(function(){var _pY=E(_pW[1]);return B(_pP(_pY[1],_pY[2]));});return function(_pZ,_q0){return new F(function(){return A(_q0,[_pX]);});};}break;default:return E(_o0);}},_q1=function(_q2){return new F(function(){return _ko(_pS,_q2);});},_q3=new T(function(){return B(unCStr("["));}),_q4=function(_q5,_q6){var _q7=function(_q8,_q9){var _qa=new T(function(){return B(A(_q9,[_1l]));}),_qb=new T(function(){var _qc=function(_qd){return new F(function(){return _q7(_cy,function(_qe){return new F(function(){return A(_q9,[[1,_qd,_qe]]);});});});};return B(A(_q5,[_jT,_qc]));}),_qf=new T(function(){return B(_jm(function(_qg){var _qh=E(_qg);if(_qh[0]==2){var _qi=E(_qh[1]);if(!_qi[0]){return [2];}else{var _qj=_qi[2];switch(E(_qi[1])){case 44:return (E(_qj)[0]==0)?(!E(_q8))?[2]:E(_qb):[2];case 93:return (E(_qj)[0]==0)?E(_qa):[2];default:return [2];}}}else{return [2];}}));}),_qk=function(_ql){return E(_qf);};return [1,function(_qm){return new F(function(){return A(_i3,[_qm,_qk]);});}];},_qn=function(_qo,_qp){return new F(function(){return _qq(_qp);});},_qr=_q6,_qs=new T(function(){var _qt=new T(function(){var _qu=new T(function(){var _qv=function(_qw){return new F(function(){return _q7(_cy,function(_qx){return new F(function(){return A(_qr,[[1,_qw,_qx]]);});});});};return B(A(_q5,[_jT,_qv]));});return B(_82(B(_q7(_cx,_qr)),_qu));});return B(_jm(function(_qy){var _qz=E(_qy);return (_qz[0]==2)?(!B(_2b(_qz[1],_q3)))?[2]:E(_qt):[2];}));}),_qA=function(_qB){return E(_qs);};return new F(function(){return _82([1,function(_qC){return new F(function(){return A(_i3,[_qC,_qA]);});}],new T(function(){return [1,B(_jU(_qn,_qr))];}));});},_qD=function(_qE,_qF){return new F(function(){return _q4(_q1,_qF);});},_qG=function(_qH){var _qI=new T(function(){return B(A(_ko,[_pS,_qH,_8Z]));});return function(_qJ){return new F(function(){return _7S(_qI,_qJ);});};},_qK=new T(function(){return B(_q4(_q1,_8Z));}),_qL=function(_q2){return new F(function(){return _7S(_qK,_q2);});},_qM=[0,_qG,_qL,_q1,_qD],_qN=function(_qO,_qP){return new F(function(){return A(_qP,[_2P]);});},_qQ=[0,_2U,_qN],_qR=[1,_qQ,_1l],_qS=function(_qT,_qU){return new F(function(){return A(_qU,[_2R]);});},_qV=[0,_2T,_qS],_qW=[1,_qV,_qR],_qX=function(_qY,_qZ,_r0){var _r1=E(_qY);if(!_r1[0]){return [2];}else{var _r2=E(_r1[1]),_r3=_r2[1],_r4=new T(function(){return B(A(_r2[2],[_qZ,_r0]));}),_r5=new T(function(){return B(_jm(function(_r6){var _r7=E(_r6);switch(_r7[0]){case 3:return (!B(_2b(_r3,_r7[1])))?[2]:E(_r4);case 4:return (!B(_2b(_r3,_r7[1])))?[2]:E(_r4);default:return [2];}}));}),_r8=function(_r9){return E(_r5);};return new F(function(){return _82([1,function(_ra){return new F(function(){return A(_i3,[_ra,_r8]);});}],new T(function(){return B(_qX(_r1[2],_qZ,_r0));}));});}},_rb=function(_rc,_rd){return new F(function(){return _qX(_qW,_rc,_rd);});},_re=function(_rf){return new F(function(){return _kd(_rb,_rf);});},_rg=function(_rh,_ri){return new F(function(){return _q4(_re,_ri);});},_rj=new T(function(){return B(_q4(_re,_8Z));}),_rk=function(_rf){return new F(function(){return _7S(_rj,_rf);});},_rl=function(_rm){var _rn=new T(function(){return B(A(_kd,[_rb,_rm,_8Z]));});return function(_qJ){return new F(function(){return _7S(_rn,_qJ);});};},_ro=[0,_rl,_rk,_re,_rg],_rp=function(_rq,_rr){var _rs=E(_rr);return (_rs[0]==0)?[0]:[1,new T(function(){return B(A(_rq,[_rs[1]]));})];},_rt=function(_ru,_rv,_){var _rw=B(A(_rv,[_]));return new T(function(){return B(_rp(_ru,_rw));});},_rx=function(_ry,_rz,_){var _rA=B(A(_rz,[_]));return new T(function(){if(!E(_rA)[0]){return [0];}else{return [1,_ry];}});},_rB=[0,_rt,_rx],_rC=function(_rD,_rE,_){var _rF=B(A(_rD,[_]));if(!E(_rF)[0]){return _6J;}else{var _rG=B(A(_rE,[_]));return (E(_rG)[0]==0)?_6J:_rG;}},_rH=function(_rI,_rJ,_){var _rK=B(A(_rI,[_])),_rL=E(_rK);if(!_rL[0]){return _6J;}else{var _rM=B(A(_rJ,[_]));return (E(_rM)[0]==0)?_6J:_rL;}},_rN=function(_rO,_){return [1,_rO];},_rP=function(_rQ){return E(E(_rQ)[2]);},_rR=function(_rS){return E(E(_rS)[4]);},_rT=function(_rU,_rV){return new F(function(){return A(_rP,[_rU,new T(function(){return B(A(_rR,[_rU,_rV]));}),function(_rW){return new F(function(){return A(_rR,[_rU,[1,_rW]]);});}]);});},_rX=function(_rY,_rZ,_s0,_s1){var _s2=new T(function(){return B(A(_rR,[_rZ,_6J]));}),_s3=function(_s4){var _s5=E(_s4);if(!_s5[0]){return E(_s2);}else{var _s6=function(_s7){var _s8=E(_s7);if(!_s8[0]){return E(_s2);}else{return new F(function(){return _rT(_rZ,new T(function(){return B(A(_s5[1],[_s8[1]]));}));});}};return new F(function(){return A(_rP,[_rZ,_s1,_s6]);});}};return new F(function(){return A(_rP,[_rZ,_s0,_s3]);});},_s9=function(_sa,_sb){return new F(function(){return _rX(_rB,_6Q,_sa,_sb);});},_sc=[0,_rB,_rN,_s9,_rC,_rH],_sd=function(_se,_sf,_){var _sg=B(A(_se,[_]));if(!E(_sg)[0]){return _6J;}else{return new F(function(){return A(_sf,[_]);});}},_sh=function(_si,_sa,_){return new F(function(){return _sd(_si,_sa,_);});},_sj=function(_sk,_sl,_){var _sm=B(A(_sk,[_])),_sn=E(_sm);if(!_sn[0]){return _6J;}else{return new F(function(){return A(_sl,[_sn[1],_]);});}},_so=function(_sp,_){return _6J;},_sq=[0,_sc,_sj,_sh,_rN,_so],_sr=function(_ss,_){return [1,B(A(_ss,[_]))];},_st=[0,_sq,_sr],_su=function(_sv,_sw,_sx,_sy,_sz,_sA,_sB,_sC){if(_sv!=_sz){return false;}else{if(E(_sw)!=E(_sA)){return false;}else{var _sD=E(_sx),_sE=E(_sB);if(E(_sD[1])!=E(_sE[1])){return false;}else{if(E(_sD[2])!=E(_sE[2])){return false;}else{return new F(function(){return _2b(_sy,_sC);});}}}}},_sF=function(_sG,_sH){var _sI=E(_sG),_sJ=E(_sI[1]),_sK=E(_sH),_sL=E(_sK[1]);return new F(function(){return _su(E(_sJ[1]),_sJ[2],_sI[2],_sI[3],E(_sL[1]),_sL[2],_sK[2],_sK[3]);});},_sM="scans",_sN=[1,_sM,_1l],_sO="calib",_sP=[1,_sO,_sN],_sQ=function(_sR){var _sS=E(_sR);return [3,[1,new T(function(){return B(_2J(_sS[1]));}),[1,new T(function(){return B(_2J(_sS[2]));}),_1l]]];},_sT=new T(function(){return [1,"Dragging"];}),_sU=[0,_1Y,_sT],_sV=new T(function(){return [1,"Free"];}),_sW="state",_sX=[0,_sW,_sV],_sY=[1,_sX,_1l],_sZ=[4,E(_sY)],_t0=function(_t1,_t2){switch(E(_t1)){case 0:return new F(function(){return _16(_29,_t2);});break;case 1:return new F(function(){return _16(_2a,_t2);});break;case 2:return new F(function(){return _16(_27,_t2);});break;default:return new F(function(){return _16(_28,_t2);});}},_t3=function(_t4){return E(toJSStr(B(_t0(_t4,_1l))));},_t5=function(_t6){return [1,B(_t3(_t6))];},_t7=function(_t8){var _t9=new T(function(){var _ta=E(E(_t8)[2]);return [3,[1,new T(function(){return B(_sQ(_ta[1]));}),[1,new T(function(){return B(_sQ(_ta[2]));}),[1,new T(function(){return B(_sQ(_ta[3]));}),[1,new T(function(){return B(_sQ(_ta[4]));}),_1l]]]]];}),_tb=new T(function(){var _tc=E(E(_t8)[1]);if(!_tc[0]){return E(_sZ);}else{return [4,[1,_sU,[1,[0,_1T,new T(function(){return B(_t5(_tc[1]));})],_1l]]];}});return [1,[0,_1S,_tb],[1,[0,_1R,_t9],_1l]];},_td="mouse",_te="scans",_tf="top",_tg="bottom",_th="offset",_ti="choice",_tj="step",_tk="rotations",_tl=[1,_tk,_1l],_tm=[1,_tj,_tl],_tn=[1,_ti,_tm],_to=[1,_th,_tn],_tp=[1,_tg,_to],_tq=[1,_tf,_tp],_tr=[1,_te,_tq],_ts=[1,_td,_tr],_tt=function(_tu,_tv){var _tw=E(_tu);if(!_tw[0]){return [0];}else{var _tx=E(_tv);return (_tx[0]==0)?[0]:[1,[0,_tw[1],_tx[1]],new T(function(){return B(_tt(_tw[2],_tx[2]));})];}},_ty=function(_tz){return new F(function(){return _tt(_ts,[1,new T(function(){if(!E(E(_tz)[1])){return [1,toJSStr(E(_33))];}else{return [1,toJSStr(E(_34))];}}),[1,new T(function(){return [3,E(B(_bc(_3B,E(_tz)[2])))];}),[1,new T(function(){return [0,E(E(_tz)[3])];}),[1,new T(function(){return [0,E(E(_tz)[4])];}),[1,new T(function(){return [0,E(E(_tz)[5])];}),[1,new T(function(){if(!E(E(_tz)[6])){return [1,toJSStr(E(_2T))];}else{return [1,toJSStr(E(_2U))];}}),[1,new T(function(){return [0,E(E(_tz)[7])];}),[1,new T(function(){return [3,E(B(_bc(_2J,E(_tz)[8])))];}),_1l]]]]]]]]);});},_tA=function(_tB){return [1,E(_tB)];},_tC="deltaZ",_tD="deltaY",_tE="deltaX",_tF=new T(function(){return B(unCStr(")"));}),_tG=new T(function(){return B(_1g(0,2,_tF));}),_tH=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_tG));}),_tI=function(_tJ){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_1g(0,_tJ,_tH));}))));});},_tK=function(_tL,_){return new T(function(){var _tM=Number(E(_tL)),_tN=jsTrunc(_tM);if(_tN<0){return B(_tI(_tN));}else{if(_tN>2){return B(_tI(_tN));}else{return _tN;}}});},_tO=0,_tP=[0,_tO,_tO,_tO],_tQ="button",_tR=new T(function(){return jsGetMouseCoords;}),_tS=function(_tT,_){var _tU=E(_tT);if(!_tU[0]){return _1l;}else{var _tV=B(_tS(_tU[2],_));return [1,new T(function(){var _tW=Number(E(_tU[1]));return jsTrunc(_tW);}),_tV];}},_tX=function(_tY,_){var _tZ=__arr2lst(0,_tY);return new F(function(){return _tS(_tZ,_);});},_u0=function(_u1,_){return new F(function(){return _tX(E(_u1),_);});},_u2=function(_u3,_){return new T(function(){var _u4=Number(E(_u3));return jsTrunc(_u4);});},_u5=[0,_u2,_u0],_u6=function(_u7,_){var _u8=E(_u7);if(!_u8[0]){return _1l;}else{var _u9=B(_u6(_u8[2],_));return [1,_u8[1],_u9];}},_ua=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_ub=[0,_6J,_6K,_1l,_ua,_6J,_6J],_uc=new T(function(){return B(_6H(_ub));}),_ud=function(_){return new F(function(){return die(_uc);});},_ue=function(_uf){return E(E(_uf)[1]);},_ug=function(_uh,_ui,_uj,_){var _uk=__arr2lst(0,_uj),_ul=B(_u6(_uk,_)),_um=E(_ul);if(!_um[0]){return new F(function(){return _ud(_);});}else{var _un=E(_um[2]);if(!_un[0]){return new F(function(){return _ud(_);});}else{if(!E(_un[2])[0]){var _uo=B(A(_ue,[_uh,_um[1],_])),_up=B(A(_ue,[_ui,_un[1],_]));return [0,_uo,_up];}else{return new F(function(){return _ud(_);});}}}},_uq=function(_){return new F(function(){return __jsNull();});},_ur=function(_us){var _ut=B(A(_us,[_]));return E(_ut);},_uu=new T(function(){return B(_ur(_uq));}),_uv=new T(function(){return E(_uu);}),_uw=function(_ux,_uy,_){if(E(_ux)==7){var _uz=E(_tR)(_uy),_uA=B(_ug(_u5,_u5,_uz,_)),_uB=_uy[E(_tE)],_uC=_uy[E(_tD)],_uD=_uy[E(_tC)];return new T(function(){return [0,E(_uA),E(_6J),[0,_uB,_uC,_uD]];});}else{var _uE=E(_tR)(_uy),_uF=B(_ug(_u5,_u5,_uE,_)),_uG=_uy[E(_tQ)],_uH=__eq(_uG,E(_uv));if(!E(_uH)){var _uI=B(_tK(_uG,_));return new T(function(){return [0,E(_uF),[1,_uI],E(_tP)];});}else{return new T(function(){return [0,E(_uF),E(_6J),E(_tP)];});}}},_uJ=function(_uK,_uL,_){return new F(function(){return _uw(_uK,E(_uL),_);});},_uM="mouseout",_uN="mouseover",_uO="mousemove",_uP="mouseup",_uQ="mousedown",_uR="dblclick",_uS="click",_uT="wheel",_uU=function(_uV){switch(E(_uV)){case 0:return E(_uS);case 1:return E(_uR);case 2:return E(_uQ);case 3:return E(_uP);case 4:return E(_uO);case 5:return E(_uN);case 6:return E(_uM);default:return E(_uT);}},_uW=[0,_uU,_uJ],_uX=function(_){return new F(function(){return E(_4)("td");});},_uY=function(_uZ){return E(E(_uZ)[1]);},_v0=function(_v1){return E(E(_v1)[3]);},_v2=(function(c,p){p.appendChild(c);}),_v3=function(_v4){return E(E(_v4)[1]);},_v5=(function(e,p,v){e.setAttribute(p, v);}),_v6=(function(e,p,v){e.style[p] = v;}),_v7=function(_v8,_v9,_va,_vb){var _vc=new T(function(){return B(A(_v3,[_v8,_va]));}),_vd=function(_ve,_){var _vf=E(_ve);if(!_vf[0]){return _a;}else{var _vg=E(_vc),_vh=E(_v2),_vi=_vh(E(_vf[1]),_vg),_vj=_vf[2];while(1){var _vk=E(_vj);if(!_vk[0]){return _a;}else{var _vl=_vh(E(_vk[1]),_vg);_vj=_vk[2];continue;}}}},_vm=function(_vn,_){while(1){var _vo=B((function(_vp,_){var _vq=E(_vp);if(!_vq[0]){return _a;}else{var _vr=_vq[2],_vs=E(_vq[1]);if(!_vs[0]){var _vt=_vs[2],_vu=E(_vs[1]);switch(_vu[0]){case 0:var _vv=E(_vc),_vw=E(_1),_vx=_vw(_vv,_vu[1],_vt),_vy=_vr;while(1){var _vz=E(_vy);if(!_vz[0]){return _a;}else{var _vA=_vz[2],_vB=E(_vz[1]);if(!_vB[0]){var _vC=_vB[2],_vD=E(_vB[1]);switch(_vD[0]){case 0:var _vE=_vw(_vv,_vD[1],_vC);_vy=_vA;continue;case 1:var _vF=E(_v6)(_vv,_vD[1],_vC);_vy=_vA;continue;default:var _vG=E(_v5)(_vv,_vD[1],_vC);_vy=_vA;continue;}}else{var _vH=B(_vd(_vB[1],_));_vy=_vA;continue;}}}break;case 1:var _vI=E(_vc),_vJ=E(_v6),_vK=_vJ(_vI,_vu[1],_vt),_vL=_vr;while(1){var _vM=E(_vL);if(!_vM[0]){return _a;}else{var _vN=_vM[2],_vO=E(_vM[1]);if(!_vO[0]){var _vP=_vO[2],_vQ=E(_vO[1]);switch(_vQ[0]){case 0:var _vR=E(_1)(_vI,_vQ[1],_vP);_vL=_vN;continue;case 1:var _vS=_vJ(_vI,_vQ[1],_vP);_vL=_vN;continue;default:var _vT=E(_v5)(_vI,_vQ[1],_vP);_vL=_vN;continue;}}else{var _vU=B(_vd(_vO[1],_));_vL=_vN;continue;}}}break;default:var _vV=E(_vc),_vW=E(_v5),_vX=_vW(_vV,_vu[1],_vt),_vY=_vr;while(1){var _vZ=E(_vY);if(!_vZ[0]){return _a;}else{var _w0=_vZ[2],_w1=E(_vZ[1]);if(!_w1[0]){var _w2=_w1[2],_w3=E(_w1[1]);switch(_w3[0]){case 0:var _w4=E(_1)(_vV,_w3[1],_w2);_vY=_w0;continue;case 1:var _w5=E(_v6)(_vV,_w3[1],_w2);_vY=_w0;continue;default:var _w6=_vW(_vV,_w3[1],_w2);_vY=_w0;continue;}}else{var _w7=B(_vd(_w1[1],_));_vY=_w0;continue;}}}}}else{var _w8=B(_vd(_vs[1],_));_vn=_vr;return null;}}})(_vn,_));if(_vo!=null){return _vo;}}};return new F(function(){return A(_2,[_v9,function(_){return new F(function(){return _vm(_vb,_);});}]);});},_w9=function(_wa,_wb,_wc,_wd){var _we=B(_uY(_wb)),_wf=function(_wg){return new F(function(){return A(_v0,[_we,new T(function(){return B(_v7(_wa,_wb,_wg,_wd));}),new T(function(){return B(A(_rR,[_we,_wg]));})]);});};return new F(function(){return A(_rP,[_we,_wc,_wf]);});},_wh=function(_wi,_){var _wj=E(_wi);if(!_wj[0]){return _1l;}else{var _wk=B(A(_w9,[_S,_6R,_uX,[1,[1,[1,_wj[1],_1l]],_1l],_])),_wl=B(_wh(_wj[2],_));return [1,_wk,_wl];}},_wm=function(_wn,_wo,_){var _wp=B(A(_w9,[_S,_6R,_uX,[1,[1,[1,_wn,_1l]],_1l],_])),_wq=B(_wh(_wo,_));return [1,_wp,_wq];},_wr=(function(s){return document.createTextNode(s);}),_ws=function(_wt,_){var _wu=jsShow(_wt),_wv=E(_wr)(toJSStr(fromJSStr(_wu)));return new F(function(){return A(_w9,[_S,_6R,_uX,[1,[1,[1,_wv,_1l]],_1l],_]);});},_ww=function(_wx,_wy,_wz){var _wA=(_wz-_wy)*25/900;if(!_wA){var _wB=rintDouble(0/_wx);return _wB&4294967295;}else{if(_wA<=0){var _wC=rintDouble( -_wA/_wx);return _wC&4294967295;}else{var _wD=rintDouble(_wA/_wx);return _wD&4294967295;}}},_wE=function(_wF,_wG){return [0,E(_wF),toJSStr(E(_wG))];},_wH=2,_wI=0,_wJ=new T(function(){return B(unCStr("x1"));}),_wK=new T(function(){return B(unCStr("y1"));}),_wL=new T(function(){return B(unCStr("x2"));}),_wM=new T(function(){return B(unCStr("y2"));}),_wN=new T(function(){return B(unCStr("frames"));}),_wO=new T(function(){return B(unCStr("time (minutes)"));}),_wP=new T(function(){return B(unCStr("title"));}),_wQ=new T(function(){return B(unCStr("Delete"));}),_wR=[1,_wQ,_1l],_wS=[1,_wP,_wR],_wT=[1,_wO,_wS],_wU=[1,_wN,_wT],_wV=[1,_wM,_wU],_wW=[1,_wL,_wV],_wX=function(_){return new F(function(){return E(_4)("span");});},_wY=new T(function(){return [0,[2,"class"],"glyphicon glyphicon-remove"];}),_wZ=[1,_wY,_1l],_x0=new T(function(){return B(_w9(_S,_6R,_wX,_wZ));}),_x1=function(_){return new F(function(){return E(_4)("input");});},_x2=function(_){return new F(function(){return E(_4)("tr");});},_x3=function(_){return new F(function(){return E(_4)("th");});},_x4=function(_){return new F(function(){return E(_4)("button");});},_x5=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_x6=function(_x7){var _x8=I_decodeDouble(_x7);return [0,[1,_x8[2]],_x8[1]];},_x9=function(_xa){var _xb=E(_xa);if(!_xb[0]){return _xb[1];}else{return new F(function(){return I_toNumber(_xb[1]);});}},_xc=function(_xd){var _xe=hs_intToInt64(2147483647),_xf=hs_leInt64(_xd,_xe);if(!_xf){return [1,I_fromInt64(_xd)];}else{var _xg=hs_intToInt64(-2147483648),_xh=hs_geInt64(_xd,_xg);if(!_xh){return [1,I_fromInt64(_xd)];}else{var _xi=hs_int64ToInt(_xd);return new F(function(){return _bg(_xi);});}}},_xj=function(_xk){var _xl=hs_intToInt64(_xk);return E(_xl);},_xm=function(_xn){var _xo=E(_xn);if(!_xo[0]){return new F(function(){return _xj(_xo[1]);});}else{return new F(function(){return I_toInt64(_xo[1]);});}},_xp=new T(function(){return [2,"value"];}),_xq=new T(function(){return [0,[2,"class"],"btn btn-danger"];}),_xr=new T(function(){return [0,[2,"type"],"text"];}),_xs=function(_xt){return E(E(_xt)[1]);},_xu=function(_xv){return E(E(_xv)[2]);},_xw=function(_xx){return E(E(_xx)[1]);},_xy=function(_){return new F(function(){return nMV(_6J);});},_xz=new T(function(){return B(_ur(_xy));}),_xA=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_xB=function(_xC){return E(E(_xC)[2]);},_xD=function(_xE,_xF,_xG,_xH,_xI,_xJ){var _xK=B(_xs(_xE)),_xL=B(_uY(_xK)),_xM=new T(function(){return B(_2(_xK));}),_xN=new T(function(){return B(_rR(_xL));}),_xO=new T(function(){return B(A(_v3,[_xF,_xH]));}),_xP=new T(function(){return B(A(_xw,[_xG,_xI]));}),_xQ=function(_xR){return new F(function(){return A(_xN,[[0,_xP,_xO,_xR]]);});},_xS=function(_xT){var _xU=new T(function(){var _xV=new T(function(){var _xW=__createJSFunc(2,function(_xX,_){var _xY=B(A(E(_xT),[_xX,_]));return _uv;}),_xZ=_xW;return function(_){return new F(function(){return E(_xA)(E(_xO),E(_xP),_xZ);});};});return B(A(_xM,[_xV]));});return new F(function(){return A(_rP,[_xL,_xU,_xQ]);});},_y0=new T(function(){var _y1=new T(function(){return B(_2(_xK));}),_y2=function(_y3){var _y4=new T(function(){return B(A(_y1,[function(_){var _=wMV(E(_xz),[1,_y3]);return new F(function(){return A(_xu,[_xG,_xI,_y3,_]);});}]));});return new F(function(){return A(_rP,[_xL,_y4,_xJ]);});};return B(A(_xB,[_xE,_y2]));});return new F(function(){return A(_rP,[_xL,_y0,_xS]);});},_y5=function(_y6,_y7){while(1){var _y8=E(_y6);if(!_y8[0]){return E(_y7);}else{var _y9=[1,_y8[1],_y7];_y6=_y8[2];_y7=_y9;continue;}}},_ya=function(_yb,_yc,_yd,_ye,_){var _yf=E(_x5)(_ye),_yg=E(_wr),_yh=_yg(toJSStr(E(_wJ))),_yi=B(A(_w9,[_S,_6R,_x3,[1,[1,[1,_yh,_1l]],_1l],_])),_yj=function(_yk,_){var _yl=E(_yk);if(!_yl[0]){return _1l;}else{var _ym=_yg(toJSStr(E(_yl[1]))),_yn=B(A(_w9,[_S,_6R,_x3,[1,[1,[1,_ym,_1l]],_1l],_])),_yo=B(_yj(_yl[2],_));return [1,_yn,_yo];}},_yp=B((function(_yq,_yr,_){var _ys=_yg(toJSStr(E(_yq))),_yt=B(A(_w9,[_S,_6R,_x3,[1,[1,[1,_ys,_1l]],_1l],_])),_yu=B(_yj(_yr,_));return [1,_yt,_yu];})(_wK,_wW,_)),_yv=B(A(_w9,[_S,_6R,_x2,[1,[1,[1,_yi,_yp]],_1l],_])),_yw=E(_v2),_yx=_yw(E(_yv),_ye),_yy=E(_yd),_yz=_yy[8],_yA=B(_y5(_yy[2],_1l));if(!_yA[0]){return _a;}else{var _yB=E(_yA[1]),_yC=E(_yB[1]),_yD=E(_yB[2]),_yE=E(_yC[1]),_yF=B(_ws(_yE*25/900,_)),_yG=_yF,_yH=E(_yC[2]),_yI=B(_ws(_yH*25/900,_)),_yJ=_yI,_yK=E(_yD[1]),_yL=B(_ws(_yK*25/900,_)),_yM=_yL,_yN=E(_yD[2]),_yO=B(_ws(_yN*25/900,_)),_yP=_yO,_yQ=E(_yy[7]),_yR=function(_yS){var _yT=B(_ws(_yS,_)),_yU=_yT,_yV=function(_yW){var _yX=rintDouble(_yW*5.8333333333333334e-2*B(_b7(_yz,0))),_yY=B(_x6(_yX)),_yZ=_yY[1],_z0=_yY[2],_z1=function(_z2){var _z3=B(_ws(_z2,_)),_z4=B(_wm(_yG,[1,_yJ,[1,_yM,[1,_yP,[1,_yU,[1,_z3,_1l]]]]],_)),_z5=B(A(_w9,[_S,_6R,_x2,[1,new T(function(){return B(_tA(_z4));}),_1l],_])),_z6=B(A(_w9,[_S,_6R,_x1,[1,_xr,[1,new T(function(){return B(_wE(_xp,_yB[3]));}),_1l]],_])),_z7=B(A(_x0,[_])),_z8=B(A(_w9,[_S,_6R,_x4,[1,_xq,[1,[1,[1,_z7,_1l]],_1l]],_])),_z9=B(A(_w9,[_S,_6R,_uX,[1,[1,[1,_z6,_1l]],_1l],_])),_za=E(_z5),_zb=_yw(E(_z9),_za),_zc=E(_z8),_zd=_yw(_zc,_za),_ze=new T(function(){return B(A(_yc,[_yB]));}),_zf=B(A(_xD,[_6S,_S,_uW,_zc,_wI,function(_zg){return E(_ze);},_])),_zh=new T(function(){return B(A(_yb,[_z6,_yB]));}),_zi=B(A(_xD,[_6S,_S,_o,_z6,_wH,function(_zj){return E(_zh);},_])),_zk=_yw(_za,_ye),_zl=function(_zm,_){var _zn=E(_zm);if(!_zn[0]){return _1l;}else{var _zo=E(_zn[1]),_zp=E(_zo[1]),_zq=E(_zo[2]),_zr=E(_zp[1]),_zs=B(_ws(_zr*25/900,_)),_zt=_zs,_zu=E(_zp[2]),_zv=B(_ws(_zu*25/900,_)),_zw=_zv,_zx=E(_zq[1]),_zy=B(_ws(_zx*25/900,_)),_zz=_zy,_zA=E(_zq[2]),_zB=B(_ws(_zA*25/900,_)),_zC=_zB,_zD=function(_zE){var _zF=B(_ws(_zE,_)),_zG=_zF,_zH=function(_zI){var _zJ=rintDouble(_zI*5.8333333333333334e-2*B(_b7(_yz,0))),_zK=B(_x6(_zJ)),_zL=_zK[1],_zM=_zK[2],_zN=function(_zO){var _zP=B(_ws(_zO,_)),_zQ=B(_wm(_zt,[1,_zw,[1,_zz,[1,_zC,[1,_zG,[1,_zP,_1l]]]]],_)),_zR=B(A(_w9,[_S,_6R,_x2,[1,new T(function(){return B(_tA(_zQ));}),_1l],_])),_zS=B(A(_w9,[_S,_6R,_x1,[1,_xr,[1,new T(function(){return B(_wE(_xp,_zo[3]));}),_1l]],_])),_zT=B(A(_x0,[_])),_zU=B(A(_w9,[_S,_6R,_x4,[1,_xq,[1,[1,[1,_zT,_1l]],_1l]],_])),_zV=B(A(_w9,[_S,_6R,_uX,[1,[1,[1,_zS,_1l]],_1l],_])),_zW=E(_zR),_zX=_yw(E(_zV),_zW),_zY=E(_zU),_zZ=_yw(_zY,_zW),_A0=new T(function(){return B(A(_yc,[_zo]));}),_A1=B(A(_xD,[_6S,_S,_uW,_zY,_wI,function(_A2){return E(_A0);},_])),_A3=new T(function(){return B(A(_yb,[_zS,_zo]));}),_A4=B(A(_xD,[_6S,_S,_o,_zS,_wH,function(_A5){return E(_A3);},_])),_A6=_yw(_zW,_ye),_A7=B(_zl(_zn[2],_));return [1,_a,_A7];};if(_zM>=0){return new F(function(){return _zN(B(_x9(B(_ou(_zL,_zM)))));});}else{var _A8=hs_uncheckedIShiftRA64(B(_xm(_zL)), -_zM);return new F(function(){return _zN(B(_x9(B(_xc(_A8)))));});}};if(_zr!=_zx){return new F(function(){return _zH(B(_ww(_yQ,_zr,_zx)));});}else{return new F(function(){return _zH(B(_ww(_yQ,_zu,_zA)));});}};if(_zr!=_zx){return new F(function(){return _zD(B(_ww(_yQ,_zr,_zx)));});}else{return new F(function(){return _zD(B(_ww(_yQ,_zu,_zA)));});}}},_A9=B(_zl(_yA[2],_));return [1,_a,_A9];};if(_z0>=0){return new F(function(){return _z1(B(_x9(B(_ou(_yZ,_z0)))));});}else{var _Aa=hs_uncheckedIShiftRA64(B(_xm(_yZ)), -_z0);return new F(function(){return _z1(B(_x9(B(_xc(_Aa)))));});}};if(_yE!=_yK){return new F(function(){return _yV(B(_ww(_yQ,_yE,_yK)));});}else{return new F(function(){return _yV(B(_ww(_yQ,_yH,_yN)));});}};if(_yE!=_yK){var _Ab=B(_yR(B(_ww(_yQ,_yE,_yK))));return _a;}else{var _Ac=B(_yR(B(_ww(_yQ,_yH,_yN))));return _a;}}},_Ad=function(_){return _a;},_Ae=(function(ctx){ctx.restore();}),_Af=(function(ctx){ctx.save();}),_Ag=(function(ctx,x,y){ctx.scale(x,y);}),_Ah=function(_Ai,_Aj,_Ak,_Al,_){var _Am=E(_Af)(_Al),_An=E(_Ag)(_Al,E(_Ai),E(_Aj)),_Ao=B(A(_Ak,[_Al,_])),_Ap=E(_Ae)(_Al);return new F(function(){return _Ad(_);});},_Aq=(function(ctx){ctx.beginPath();}),_Ar=(function(ctx){ctx.stroke();}),_As=function(_At,_Au,_){var _Av=E(_Aq)(_Au),_Aw=B(A(_At,[_Au,_])),_Ax=E(_Ar)(_Au);return new F(function(){return _Ad(_);});},_Ay=(function(ctx,i,x,y){ctx.drawImage(i,x,y);}),_Az=function(_AA,_AB,_AC,_AD,_){var _AE=E(_Ay)(_AD,_AA,_AB,_AC);return new F(function(){return _Ad(_);});},_AF=",",_AG="[",_AH="]",_AI="{",_AJ="}",_AK=":",_AL="\"",_AM="true",_AN="false",_AO="null",_AP=new T(function(){return JSON.stringify;}),_AQ=function(_AR,_AS){var _AT=E(_AS);switch(_AT[0]){case 0:return [0,new T(function(){return jsShow(_AT[1]);}),_AR];case 1:return [0,new T(function(){var _AU=E(_AP)(_AT[1]);return String(_AU);}),_AR];case 2:return (!E(_AT[1]))?[0,_AN,_AR]:[0,_AM,_AR];case 3:var _AV=E(_AT[1]);if(!_AV[0]){return [0,_AG,[1,_AH,_AR]];}else{var _AW=new T(function(){var _AX=new T(function(){var _AY=function(_AZ){var _B0=E(_AZ);if(!_B0[0]){return [1,_AH,_AR];}else{var _B1=new T(function(){var _B2=B(_AQ(new T(function(){return B(_AY(_B0[2]));}),_B0[1]));return [1,_B2[1],_B2[2]];});return [1,_AF,_B1];}};return B(_AY(_AV[2]));}),_B3=B(_AQ(_AX,_AV[1]));return [1,_B3[1],_B3[2]];});return [0,_AG,_AW];}break;case 4:var _B4=E(_AT[1]);if(!_B4[0]){return [0,_AI,[1,_AJ,_AR]];}else{var _B5=E(_B4[1]),_B6=new T(function(){var _B7=new T(function(){var _B8=function(_B9){var _Ba=E(_B9);if(!_Ba[0]){return [1,_AJ,_AR];}else{var _Bb=E(_Ba[1]),_Bc=new T(function(){var _Bd=B(_AQ(new T(function(){return B(_B8(_Ba[2]));}),_Bb[2]));return [1,_Bd[1],_Bd[2]];});return [1,_AF,[1,_AL,[1,_Bb[1],[1,_AL,[1,_AK,_Bc]]]]];}};return B(_B8(_B4[2]));}),_Be=B(_AQ(_B7,_B5[2]));return [1,_Be[1],_Be[2]];});return [0,_AI,[1,new T(function(){var _Bf=E(_AP)(E(_B5[1]));return String(_Bf);}),[1,_AK,_B6]]];}break;default:return [0,_AO,_AR];}},_Bg=new T(function(){return toJSStr(_1l);}),_Bh=function(_Bi){var _Bj=B(_AQ(_1l,_Bi)),_Bk=jsCat([1,_Bj[1],_Bj[2]],E(_Bg));return E(_Bk);},_Bl=function(_Bm){while(1){var _Bn=E(_Bm);if(!_Bn[0]){_Bm=[1,I_fromInt(_Bn[1])];continue;}else{return new F(function(){return I_toString(_Bn[1]);});}}},_Bo=function(_Bp,_Bq){return new F(function(){return _16(fromJSStr(B(_Bl(_Bp))),_Bq);});},_Br=[0,0],_Bs=function(_Bt,_Bu,_Bv){if(_Bt<=6){return new F(function(){return _Bo(_Bu,_Bv);});}else{if(!B(_mD(_Bu,_Br))){return new F(function(){return _Bo(_Bu,_Bv);});}else{return [1,_1f,new T(function(){return B(_16(fromJSStr(B(_Bl(_Bu))),[1,_1e,_Bv]));})];}}},_Bw=0,_Bx=1,_By=function(_Bz){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_Bz));}))));});},_BA=new T(function(){return B(_By("ww_slRl MouseState"));}),_BB=function(_BC){var _BD=E(_BC);if(!_BD[0]){return [0];}else{return new F(function(){return _16(_BD[1],new T(function(){return B(_BB(_BD[2]));},1));});}},_BE=new T(function(){return B(unCStr("\r\n"));}),_BF=new T(function(){return B(_16(_BE,_BE));}),_BG=function(_BH,_BI){var _BJ=E(_BI);return (_BJ[0]==0)?[0]:[1,_BH,[1,_BJ[1],new T(function(){return B(_BG(_BH,_BJ[2]));})]];},_BK=new T(function(){return B(unCStr("printf: formatting string ended prematurely"));}),_BL=new T(function(){return B(err(_BK));}),_BM=function(_BN,_BO){var _BP=E(_BO);return (_BP[0]==0)?E(_BL):[0,_1l,_BP[1],_BP[2]];},_BQ=new T(function(){return B(unCStr("!!: negative index"));}),_BR=new T(function(){return B(unCStr("Prelude."));}),_BS=new T(function(){return B(_16(_BR,_BQ));}),_BT=new T(function(){return B(err(_BS));}),_BU=new T(function(){return B(unCStr("!!: index too large"));}),_BV=new T(function(){return B(_16(_BR,_BU));}),_BW=new T(function(){return B(err(_BV));}),_BX=function(_BY,_BZ){while(1){var _C0=E(_BY);if(!_C0[0]){return E(_BW);}else{var _C1=E(_BZ);if(!_C1){return E(_C0[1]);}else{_BY=_C0[2];_BZ=_C1-1|0;continue;}}}},_C2=function(_C3,_C4){if(_C4>=0){return new F(function(){return _BX(_C3,_C4);});}else{return E(_BT);}},_C5=new T(function(){return B(unCStr("ACK"));}),_C6=new T(function(){return B(unCStr("BEL"));}),_C7=new T(function(){return B(unCStr("BS"));}),_C8=new T(function(){return B(unCStr("SP"));}),_C9=[1,_C8,_1l],_Ca=new T(function(){return B(unCStr("US"));}),_Cb=[1,_Ca,_C9],_Cc=new T(function(){return B(unCStr("RS"));}),_Cd=[1,_Cc,_Cb],_Ce=new T(function(){return B(unCStr("GS"));}),_Cf=[1,_Ce,_Cd],_Cg=new T(function(){return B(unCStr("FS"));}),_Ch=[1,_Cg,_Cf],_Ci=new T(function(){return B(unCStr("ESC"));}),_Cj=[1,_Ci,_Ch],_Ck=new T(function(){return B(unCStr("SUB"));}),_Cl=[1,_Ck,_Cj],_Cm=new T(function(){return B(unCStr("EM"));}),_Cn=[1,_Cm,_Cl],_Co=new T(function(){return B(unCStr("CAN"));}),_Cp=[1,_Co,_Cn],_Cq=new T(function(){return B(unCStr("ETB"));}),_Cr=[1,_Cq,_Cp],_Cs=new T(function(){return B(unCStr("SYN"));}),_Ct=[1,_Cs,_Cr],_Cu=new T(function(){return B(unCStr("NAK"));}),_Cv=[1,_Cu,_Ct],_Cw=new T(function(){return B(unCStr("DC4"));}),_Cx=[1,_Cw,_Cv],_Cy=new T(function(){return B(unCStr("DC3"));}),_Cz=[1,_Cy,_Cx],_CA=new T(function(){return B(unCStr("DC2"));}),_CB=[1,_CA,_Cz],_CC=new T(function(){return B(unCStr("DC1"));}),_CD=[1,_CC,_CB],_CE=new T(function(){return B(unCStr("DLE"));}),_CF=[1,_CE,_CD],_CG=new T(function(){return B(unCStr("SI"));}),_CH=[1,_CG,_CF],_CI=new T(function(){return B(unCStr("SO"));}),_CJ=[1,_CI,_CH],_CK=new T(function(){return B(unCStr("CR"));}),_CL=[1,_CK,_CJ],_CM=new T(function(){return B(unCStr("FF"));}),_CN=[1,_CM,_CL],_CO=new T(function(){return B(unCStr("VT"));}),_CP=[1,_CO,_CN],_CQ=new T(function(){return B(unCStr("LF"));}),_CR=[1,_CQ,_CP],_CS=new T(function(){return B(unCStr("HT"));}),_CT=[1,_CS,_CR],_CU=[1,_C7,_CT],_CV=[1,_C6,_CU],_CW=[1,_C5,_CV],_CX=new T(function(){return B(unCStr("ENQ"));}),_CY=[1,_CX,_CW],_CZ=new T(function(){return B(unCStr("EOT"));}),_D0=[1,_CZ,_CY],_D1=new T(function(){return B(unCStr("ETX"));}),_D2=[1,_D1,_D0],_D3=new T(function(){return B(unCStr("STX"));}),_D4=[1,_D3,_D2],_D5=new T(function(){return B(unCStr("SOH"));}),_D6=[1,_D5,_D4],_D7=new T(function(){return B(unCStr("NUL"));}),_D8=[1,_D7,_D6],_D9=92,_Da=new T(function(){return B(unCStr("\\DEL"));}),_Db=new T(function(){return B(unCStr("\\a"));}),_Dc=new T(function(){return B(unCStr("\\\\"));}),_Dd=new T(function(){return B(unCStr("\\SO"));}),_De=new T(function(){return B(unCStr("\\r"));}),_Df=new T(function(){return B(unCStr("\\f"));}),_Dg=new T(function(){return B(unCStr("\\v"));}),_Dh=new T(function(){return B(unCStr("\\n"));}),_Di=new T(function(){return B(unCStr("\\t"));}),_Dj=new T(function(){return B(unCStr("\\b"));}),_Dk=function(_Dl,_Dm){if(_Dl<=127){var _Dn=E(_Dl);switch(_Dn){case 92:return new F(function(){return _16(_Dc,_Dm);});break;case 127:return new F(function(){return _16(_Da,_Dm);});break;default:if(_Dn<32){var _Do=E(_Dn);switch(_Do){case 7:return new F(function(){return _16(_Db,_Dm);});break;case 8:return new F(function(){return _16(_Dj,_Dm);});break;case 9:return new F(function(){return _16(_Di,_Dm);});break;case 10:return new F(function(){return _16(_Dh,_Dm);});break;case 11:return new F(function(){return _16(_Dg,_Dm);});break;case 12:return new F(function(){return _16(_Df,_Dm);});break;case 13:return new F(function(){return _16(_De,_Dm);});break;case 14:return new F(function(){return _16(_Dd,new T(function(){var _Dp=E(_Dm);if(!_Dp[0]){return [0];}else{if(E(_Dp[1])==72){return B(unAppCStr("\\&",_Dp));}else{return E(_Dp);}}},1));});break;default:return new F(function(){return _16([1,_D9,new T(function(){return B(_C2(_D8,_Do));})],_Dm);});}}else{return [1,_Dn,_Dm];}}}else{var _Dq=new T(function(){var _Dr=jsShowI(_Dl);return B(_16(fromJSStr(_Dr),new T(function(){var _Ds=E(_Dm);if(!_Ds[0]){return [0];}else{var _Dt=E(_Ds[1]);if(_Dt<48){return E(_Ds);}else{if(_Dt>57){return E(_Ds);}else{return B(unAppCStr("\\&",_Ds));}}}},1)));});return [1,_D9,_Dq];}},_Du=39,_Dv=[1,_Du,_1l],_Dw=new T(function(){return B(unCStr("\'\\\'\'"));}),_Dx=new T(function(){return B(_16(_Dw,_1l));}),_Dy=function(_Dz){var _DA=new T(function(){var _DB=new T(function(){var _DC=E(_Dz);if(_DC==39){return E(_Dx);}else{return [1,_Du,new T(function(){return B(_Dk(_DC,_Dv));})];}});return B(unAppCStr("bad formatting char ",_DB));});return new F(function(){return err(B(unAppCStr("printf: ",_DA)));});},_DD=new T(function(){return B(unCStr("-"));}),_DE=new T(function(){return B(unCStr("printf: internal error: impossible dfmt"));}),_DF=new T(function(){return B(err(_DE));}),_DG=function(_DH){var _DI=E(_DH);return new F(function(){return Math.log(_DI+(_DI+1)*Math.sqrt((_DI-1)/(_DI+1)));});},_DJ=function(_DK){var _DL=E(_DK);return new F(function(){return Math.log(_DL+Math.sqrt(1+_DL*_DL));});},_DM=function(_DN){var _DO=E(_DN);return 0.5*Math.log((1+_DO)/(1-_DO));},_DP=function(_DQ,_DR){return Math.log(E(_DR))/Math.log(E(_DQ));},_DS=3.141592653589793,_DT=function(_DU){var _DV=E(_DU);return new F(function(){return _pP(_DV[1],_DV[2]);});},_DW=function(_DX){return 1/E(_DX);},_DY=function(_DZ){var _E0=E(_DZ),_E1=E(_E0);return (_E1==0)?E(_pO):(_E1<=0)? -_E1:E(_E0);},_E2=function(_E3){return new F(function(){return _x9(_E3);});},_E4=1,_E5=-1,_E6=function(_E7){var _E8=E(_E7);return (_E8<=0)?(_E8>=0)?E(_E8):E(_E5):E(_E4);},_E9=function(_Ea,_Eb){return E(_Ea)-E(_Eb);},_Ec=function(_Ed){return  -E(_Ed);},_Ee=function(_Ef,_Eg){return E(_Ef)+E(_Eg);},_Eh=function(_Ei,_Ej){return E(_Ei)*E(_Ej);},_Ek=[0,_Ee,_E9,_Eh,_Ec,_DY,_E6,_E2],_El=function(_Em,_En){return E(_Em)/E(_En);},_Eo=[0,_Ek,_El,_DW,_DT],_Ep=function(_Eq){return new F(function(){return Math.acos(E(_Eq));});},_Er=function(_Es){return new F(function(){return Math.asin(E(_Es));});},_Et=function(_Eu){return new F(function(){return Math.atan(E(_Eu));});},_Ev=function(_Ew){return new F(function(){return Math.cos(E(_Ew));});},_Ex=function(_Ey){return new F(function(){return cosh(E(_Ey));});},_Ez=function(_EA){return new F(function(){return Math.exp(E(_EA));});},_EB=function(_EC){return new F(function(){return Math.log(E(_EC));});},_ED=function(_EE,_EF){return new F(function(){return Math.pow(E(_EE),E(_EF));});},_EG=function(_EH){return new F(function(){return Math.sin(E(_EH));});},_EI=function(_EJ){return new F(function(){return sinh(E(_EJ));});},_EK=function(_EL){return new F(function(){return Math.sqrt(E(_EL));});},_EM=function(_EN){return new F(function(){return Math.tan(E(_EN));});},_EO=function(_EP){return new F(function(){return tanh(E(_EP));});},_EQ=[0,_Eo,_DS,_Ez,_EB,_EK,_ED,_DP,_EG,_Ev,_EM,_Er,_Ep,_Et,_EI,_Ex,_EO,_DJ,_DG,_DM],_ER=function(_ES,_ET){if(_ET<=0){var _EU=function(_EV){var _EW=function(_EX){var _EY=function(_EZ){var _F0=function(_F1){var _F2=isDoubleNegativeZero(_ET),_F3=_F2,_F4=function(_F5){var _F6=E(_ES);if(!_F6){return (_ET>=0)?(E(_F3)==0)?E(_ET):3.141592653589793:3.141592653589793;}else{var _F7=E(_ET);return (_F7==0)?E(_F6):_F7+_F6;}};if(!E(_F3)){return new F(function(){return _F4(_);});}else{var _F8=E(_ES),_F9=isDoubleNegativeZero(_F8);if(!E(_F9)){return new F(function(){return _F4(_);});}else{return  -B(_ER( -_F8,_ET));}}};if(_ET>=0){return new F(function(){return _F0(_);});}else{var _Fa=E(_ES),_Fb=isDoubleNegativeZero(_Fa);if(!E(_Fb)){return new F(function(){return _F0(_);});}else{return  -B(_ER( -_Fa,_ET));}}};if(_ET>0){return new F(function(){return _EY(_);});}else{var _Fc=E(_ES);if(_Fc>=0){return new F(function(){return _EY(_);});}else{return  -B(_ER( -_Fc,_ET));}}};if(_ET>=0){return new F(function(){return _EW(_);});}else{var _Fd=E(_ES);if(_Fd<=0){return new F(function(){return _EW(_);});}else{return 3.141592653589793+Math.atan(_Fd/_ET);}}};if(!E(_ET)){if(E(_ES)<=0){return new F(function(){return _EU(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _EU(_);});}}else{return new F(function(){return Math.atan(E(_ES)/_ET);});}},_Fe=function(_Ff,_Fg){return new F(function(){return _ER(_Ff,E(_Fg));});},_Fh=function(_Fi){var _Fj=B(_x6(E(_Fi)));return [0,_Fj[1],_Fj[2]];},_Fk=function(_Fl,_Fm){return new F(function(){return _og(_Fl,E(_Fm));});},_Fn=function(_Fo){var _Fp=B(_x6(_Fo));return (!B(_lu(_Fp[1],_ot)))?_Fp[2]+53|0:0;},_Fq=function(_Fr){return new F(function(){return _Fn(E(_Fr));});},_Fs=53,_Ft=function(_Fu){return E(_Fs);},_Fv=[0,2],_Fw=function(_Fx){return E(_Fv);},_Fy=[0,_kU,_kT],_Fz=function(_FA){return E(_Fy);},_FB=function(_FC){var _FD=isDoubleDenormalized(E(_FC));return (E(_FD)==0)?false:true;},_FE=function(_FF){return true;},_FG=function(_FH){var _FI=isDoubleInfinite(E(_FH));return (E(_FI)==0)?false:true;},_FJ=function(_FK){var _FL=isDoubleNaN(E(_FK));return (E(_FL)==0)?false:true;},_FM=function(_FN){var _FO=isDoubleNegativeZero(E(_FN));return (E(_FO)==0)?false:true;},_FP=function(_FQ,_FR){var _FS=E(_FQ);if(!_FS){return E(_FR);}else{var _FT=E(_FR);if(!_FT){return 0;}else{var _FU=isDoubleFinite(_FT);if(!E(_FU)){return E(_FT);}else{var _FV=B(_x6(_FT)),_FW=_FV[1],_FX=_FV[2];if(2257>_FS){if(-2257>_FS){return new F(function(){return _og(_FW,_FX+(-2257)|0);});}else{return new F(function(){return _og(_FW,_FX+_FS|0);});}}else{return new F(function(){return _og(_FW,_FX+2257|0);});}}}}},_FY=function(_FZ,_G0){return new F(function(){return _FP(E(_FZ),E(_G0));});},_G1=function(_G2){return new F(function(){return _og(B(_x6(E(_G2)))[1],-53);});},_G3=function(_G4,_G5){return (E(_G4)!=E(_G5))?true:false;},_G6=function(_G7,_G8){return E(_G7)==E(_G8);},_G9=[0,_G6,_G3],_Ga=function(_Gb,_Gc){return E(_Gb)<E(_Gc);},_Gd=function(_Ge,_Gf){return E(_Ge)<=E(_Gf);},_Gg=function(_Gh,_Gi){return E(_Gh)>E(_Gi);},_Gj=function(_Gk,_Gl){return E(_Gk)>=E(_Gl);},_Gm=function(_Gn,_Go){var _Gp=E(_Gn),_Gq=E(_Go);return (_Gp>=_Gq)?(_Gp!=_Gq)?2:1:0;},_Gr=function(_Gs,_Gt){var _Gu=E(_Gs),_Gv=E(_Gt);return (_Gu>_Gv)?E(_Gu):E(_Gv);},_Gw=function(_Gx,_Gy){var _Gz=E(_Gx),_GA=E(_Gy);return (_Gz>_GA)?E(_GA):E(_Gz);},_GB=[0,_G9,_Gm,_Ga,_Gd,_Gg,_Gj,_Gr,_Gw],_GC=new T(function(){var _GD=newByteArr(256),_GE=_GD,_=_GE["v"]["i8"][0]=8,_GF=function(_GG,_GH,_GI,_){while(1){if(_GI>=256){if(_GG>=256){return E(_);}else{var _GJ=imul(2,_GG)|0,_GK=_GH+1|0,_GL=_GG;_GG=_GJ;_GH=_GK;_GI=_GL;continue;}}else{var _=_GE["v"]["i8"][_GI]=_GH,_GL=_GI+_GG|0;_GI=_GL;continue;}}},_=B(_GF(2,0,1,_));return _GE;}),_GM=function(_GN,_GO){while(1){var _GP=B((function(_GQ,_GR){var _GS=hs_int64ToInt(_GQ),_GT=E(_GC)["v"]["i8"][(255&_GS>>>0)>>>0&4294967295];if(_GR>_GT){if(_GT>=8){var _GU=hs_uncheckedIShiftRA64(_GQ,8),_GV=_GR-8|0;_GN=_GU;_GO=_GV;return null;}else{return [0,new T(function(){var _GW=hs_uncheckedIShiftRA64(_GQ,_GT);return B(_xc(_GW));}),_GR-_GT|0];}}else{return [0,new T(function(){var _GX=hs_uncheckedIShiftRA64(_GQ,_GR);return B(_xc(_GX));}),0];}})(_GN,_GO));if(_GP!=null){return _GP;}}},_GY=function(_GZ){return I_toInt(_GZ)>>>0;},_H0=function(_H1){var _H2=E(_H1);if(!_H2[0]){return _H2[1]>>>0;}else{return new F(function(){return _GY(_H2[1]);});}},_H3=function(_H4){var _H5=B(_x6(_H4)),_H6=_H5[1],_H7=_H5[2];if(_H7<0){var _H8=function(_H9){if(!_H9){return [0,E(_H6),B(_ou(_o3, -_H7))];}else{var _Ha=B(_GM(B(_xm(_H6)), -_H7));return [0,E(_Ha[1]),B(_ou(_o3,_Ha[2]))];}};if(!((B(_H0(_H6))&1)>>>0)){return new F(function(){return _H8(1);});}else{return new F(function(){return _H8(0);});}}else{return [0,B(_ou(_H6,_H7)),_o3];}},_Hb=function(_Hc){var _Hd=B(_H3(E(_Hc)));return [0,E(_Hd[1]),E(_Hd[2])];},_He=[0,_Ek,_GB,_Hb],_Hf=function(_Hg){return E(E(_Hg)[1]);},_Hh=function(_Hi){return E(E(_Hi)[1]);},_Hj=function(_Hk,_Hl){if(_Hk<=_Hl){var _Hm=function(_Hn){return [1,_Hn,new T(function(){if(_Hn!=_Hl){return B(_Hm(_Hn+1|0));}else{return [0];}})];};return new F(function(){return _Hm(_Hk);});}else{return [0];}},_Ho=function(_Hp){return new F(function(){return _Hj(E(_Hp),2147483647);});},_Hq=function(_Hr,_Hs,_Ht){if(_Ht<=_Hs){var _Hu=new T(function(){var _Hv=_Hs-_Hr|0,_Hw=function(_Hx){return (_Hx>=(_Ht-_Hv|0))?[1,_Hx,new T(function(){return B(_Hw(_Hx+_Hv|0));})]:[1,_Hx,_1l];};return B(_Hw(_Hs));});return [1,_Hr,_Hu];}else{return (_Ht<=_Hr)?[1,_Hr,_1l]:[0];}},_Hy=function(_Hz,_HA,_HB){if(_HB>=_HA){var _HC=new T(function(){var _HD=_HA-_Hz|0,_HE=function(_HF){return (_HF<=(_HB-_HD|0))?[1,_HF,new T(function(){return B(_HE(_HF+_HD|0));})]:[1,_HF,_1l];};return B(_HE(_HA));});return [1,_Hz,_HC];}else{return (_HB>=_Hz)?[1,_Hz,_1l]:[0];}},_HG=function(_HH,_HI){if(_HI<_HH){return new F(function(){return _Hq(_HH,_HI,-2147483648);});}else{return new F(function(){return _Hy(_HH,_HI,2147483647);});}},_HJ=function(_HK,_HL){return new F(function(){return _HG(E(_HK),E(_HL));});},_HM=function(_HN,_HO,_HP){if(_HO<_HN){return new F(function(){return _Hq(_HN,_HO,_HP);});}else{return new F(function(){return _Hy(_HN,_HO,_HP);});}},_HQ=function(_HR,_HS,_HT){return new F(function(){return _HM(E(_HR),E(_HS),E(_HT));});},_HU=function(_HV,_HW){return new F(function(){return _Hj(E(_HV),E(_HW));});},_HX=function(_HY){return E(_HY);},_HZ=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_I0=new T(function(){return B(err(_HZ));}),_I1=function(_I2){var _I3=E(_I2);return (_I3==(-2147483648))?E(_I0):_I3-1|0;},_I4=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_I5=new T(function(){return B(err(_I4));}),_I6=function(_I7){var _I8=E(_I7);return (_I8==2147483647)?E(_I5):_I8+1|0;},_I9=[0,_I6,_I1,_HX,_HX,_Ho,_HJ,_HU,_HQ],_Ia=function(_Ib,_Ic){if(_Ib<=0){if(_Ib>=0){return new F(function(){return quot(_Ib,_Ic);});}else{if(_Ic<=0){return new F(function(){return quot(_Ib,_Ic);});}else{return quot(_Ib+1|0,_Ic)-1|0;}}}else{if(_Ic>=0){if(_Ib>=0){return new F(function(){return quot(_Ib,_Ic);});}else{if(_Ic<=0){return new F(function(){return quot(_Ib,_Ic);});}else{return quot(_Ib+1|0,_Ic)-1|0;}}}else{return quot(_Ib-1|0,_Ic)-1|0;}}},_Id=0,_Ie=new T(function(){return B(_lq(_Id));}),_If=new T(function(){return die(_Ie);}),_Ig=function(_Ih,_Ii){var _Ij=E(_Ii);switch(_Ij){case -1:var _Ik=E(_Ih);if(_Ik==(-2147483648)){return E(_If);}else{return new F(function(){return _Ia(_Ik,-1);});}break;case 0:return E(_lt);default:return new F(function(){return _Ia(_Ih,_Ij);});}},_Il=function(_Im,_In){return new F(function(){return _Ig(E(_Im),E(_In));});},_Io=0,_Ip=[0,_If,_Io],_Iq=function(_Ir,_Is){var _It=E(_Ir),_Iu=E(_Is);switch(_Iu){case -1:var _Iv=E(_It);if(_Iv==(-2147483648)){return E(_Ip);}else{if(_Iv<=0){if(_Iv>=0){var _Iw=quotRemI(_Iv,-1);return [0,_Iw[1],_Iw[2]];}else{var _Ix=quotRemI(_Iv,-1);return [0,_Ix[1],_Ix[2]];}}else{var _Iy=quotRemI(_Iv-1|0,-1);return [0,_Iy[1]-1|0,(_Iy[2]+(-1)|0)+1|0];}}break;case 0:return E(_lt);default:if(_It<=0){if(_It>=0){var _Iz=quotRemI(_It,_Iu);return [0,_Iz[1],_Iz[2]];}else{if(_Iu<=0){var _IA=quotRemI(_It,_Iu);return [0,_IA[1],_IA[2]];}else{var _IB=quotRemI(_It+1|0,_Iu);return [0,_IB[1]-1|0,(_IB[2]+_Iu|0)-1|0];}}}else{if(_Iu>=0){if(_It>=0){var _IC=quotRemI(_It,_Iu);return [0,_IC[1],_IC[2]];}else{if(_Iu<=0){var _ID=quotRemI(_It,_Iu);return [0,_ID[1],_ID[2]];}else{var _IE=quotRemI(_It+1|0,_Iu);return [0,_IE[1]-1|0,(_IE[2]+_Iu|0)-1|0];}}}else{var _IF=quotRemI(_It-1|0,_Iu);return [0,_IF[1]-1|0,(_IF[2]+_Iu|0)+1|0];}}}},_IG=function(_IH,_II){var _IJ=_IH%_II;if(_IH<=0){if(_IH>=0){return E(_IJ);}else{if(_II<=0){return E(_IJ);}else{var _IK=E(_IJ);return (_IK==0)?0:_IK+_II|0;}}}else{if(_II>=0){if(_IH>=0){return E(_IJ);}else{if(_II<=0){return E(_IJ);}else{var _IL=E(_IJ);return (_IL==0)?0:_IL+_II|0;}}}else{var _IM=E(_IJ);return (_IM==0)?0:_IM+_II|0;}}},_IN=function(_IO,_IP){var _IQ=E(_IP);switch(_IQ){case -1:return E(_Io);case 0:return E(_lt);default:return new F(function(){return _IG(E(_IO),_IQ);});}},_IR=function(_IS,_IT){var _IU=E(_IS),_IV=E(_IT);switch(_IV){case -1:var _IW=E(_IU);if(_IW==(-2147483648)){return E(_If);}else{return new F(function(){return quot(_IW,-1);});}break;case 0:return E(_lt);default:return new F(function(){return quot(_IU,_IV);});}},_IX=function(_IY,_IZ){var _J0=E(_IY),_J1=E(_IZ);switch(_J1){case -1:var _J2=E(_J0);if(_J2==(-2147483648)){return E(_Ip);}else{var _J3=quotRemI(_J2,-1);return [0,_J3[1],_J3[2]];}break;case 0:return E(_lt);default:var _J4=quotRemI(_J0,_J1);return [0,_J4[1],_J4[2]];}},_J5=function(_J6,_J7){var _J8=E(_J7);switch(_J8){case -1:return E(_Io);case 0:return E(_lt);default:return E(_J6)%_J8;}},_J9=function(_Ja){return new F(function(){return _bg(E(_Ja));});},_Jb=function(_Jc){return [0,E(B(_bg(E(_Jc)))),E(_md)];},_Jd=function(_Je,_Jf){return imul(E(_Je),E(_Jf))|0;},_Jg=function(_Jh,_Ji){return E(_Jh)+E(_Ji)|0;},_Jj=function(_Jk,_Jl){return E(_Jk)-E(_Jl)|0;},_Jm=function(_Jn){var _Jo=E(_Jn);return (_Jo<0)? -_Jo:E(_Jo);},_Jp=function(_Jq){return new F(function(){return _cK(_Jq);});},_Jr=function(_Js){return  -E(_Js);},_Jt=-1,_Ju=0,_Jv=1,_Jw=function(_Jx){var _Jy=E(_Jx);return (_Jy>=0)?(E(_Jy)==0)?E(_Ju):E(_Jv):E(_Jt);},_Jz=[0,_Jg,_Jj,_Jd,_Jr,_Jm,_Jw,_Jp],_JA=function(_JB,_JC){return E(_JB)!=E(_JC);},_JD=[0,_nB,_JA],_JE=function(_JF,_JG){var _JH=E(_JF),_JI=E(_JG);return (_JH>_JI)?E(_JH):E(_JI);},_JJ=function(_JK,_JL){var _JM=E(_JK),_JN=E(_JL);return (_JM>_JN)?E(_JN):E(_JM);},_JO=function(_JP,_JQ){return (_JP>=_JQ)?(_JP!=_JQ)?2:1:0;},_JR=function(_JS,_JT){return new F(function(){return _JO(E(_JS),E(_JT));});},_JU=function(_JV,_JW){return E(_JV)>=E(_JW);},_JX=function(_JY,_JZ){return E(_JY)>E(_JZ);},_K0=function(_K1,_K2){return E(_K1)<=E(_K2);},_K3=function(_K4,_K5){return E(_K4)<E(_K5);},_K6=[0,_JD,_JR,_K3,_K0,_JX,_JU,_JE,_JJ],_K7=[0,_Jz,_K6,_Jb],_K8=[0,_K7,_I9,_IR,_J5,_Il,_IN,_IX,_Iq,_J9],_K9=function(_Ka,_Kb,_Kc){while(1){if(!(_Kb%2)){var _Kd=B(_bm(_Ka,_Ka)),_Ke=quot(_Kb,2);_Ka=_Kd;_Kb=_Ke;continue;}else{var _Kf=E(_Kb);if(_Kf==1){return new F(function(){return _bm(_Ka,_Kc);});}else{var _Kd=B(_bm(_Ka,_Ka)),_Kg=B(_bm(_Ka,_Kc));_Ka=_Kd;_Kb=quot(_Kf-1|0,2);_Kc=_Kg;continue;}}}},_Kh=function(_Ki,_Kj){while(1){if(!(_Kj%2)){var _Kk=B(_bm(_Ki,_Ki)),_Kl=quot(_Kj,2);_Ki=_Kk;_Kj=_Kl;continue;}else{var _Km=E(_Kj);if(_Km==1){return E(_Ki);}else{return new F(function(){return _K9(B(_bm(_Ki,_Ki)),quot(_Km-1|0,2),_Ki);});}}}},_Kn=function(_Ko){return E(E(_Ko)[3]);},_Kp=function(_Kq){return E(E(_Kq)[1]);},_Kr=function(_Ks){return E(E(_Ks)[2]);},_Kt=function(_Ku){return E(E(_Ku)[2]);},_Kv=function(_Kw){return E(E(_Kw)[3]);},_Kx=function(_Ky){return E(E(_Ky)[7]);},_Kz=function(_KA){return E(E(_KA)[4]);},_KB=function(_KC,_KD){var _KE=B(_Hf(_KC)),_KF=new T(function(){return B(_Hh(_KE));}),_KG=new T(function(){return B(A(_Kz,[_KC,_KD,new T(function(){return B(A(_Kx,[_KF,_mg]));})]));});return new F(function(){return A(_T,[B(_Kp(B(_Kr(_KE)))),_KG,new T(function(){return B(A(_Kx,[_KF,_lC]));})]);});},_KH=new T(function(){return B(err(_me));}),_KI=function(_KJ){return E(E(_KJ)[3]);},_KK=function(_KL,_KM,_KN,_KO){var _KP=B(_Hf(_KM)),_KQ=new T(function(){return B(_Hh(_KP));}),_KR=B(_Kr(_KP));if(!B(A(_Kv,[_KR,_KO,new T(function(){return B(A(_Kx,[_KQ,_lC]));})]))){if(!B(A(_T,[B(_Kp(_KR)),_KO,new T(function(){return B(A(_Kx,[_KQ,_lC]));})]))){var _KS=new T(function(){return B(A(_Kx,[_KQ,_mg]));}),_KT=new T(function(){return B(A(_Kx,[_KQ,_md]));}),_KU=B(_Kp(_KR)),_KV=function(_KW,_KX,_KY){while(1){var _KZ=B((function(_L0,_L1,_L2){if(!B(_KB(_KM,_L1))){if(!B(A(_T,[_KU,_L1,_KT]))){var _L3=new T(function(){return B(A(_KI,[_KM,new T(function(){return B(A(_Kt,[_KQ,_L1,_KT]));}),_KS]));});_KW=new T(function(){return B(A(_Kn,[_KL,_L0,_L0]));});_KX=_L3;_KY=new T(function(){return B(A(_Kn,[_KL,_L0,_L2]));});return null;}else{return new F(function(){return A(_Kn,[_KL,_L0,_L2]);});}}else{var _L4=_L2;_KW=new T(function(){return B(A(_Kn,[_KL,_L0,_L0]));});_KX=new T(function(){return B(A(_KI,[_KM,_L1,_KS]));});_KY=_L4;return null;}})(_KW,_KX,_KY));if(_KZ!=null){return _KZ;}}},_L5=_KN,_L6=_KO;while(1){var _L7=B((function(_L8,_L9){if(!B(_KB(_KM,_L9))){if(!B(A(_T,[_KU,_L9,_KT]))){var _La=new T(function(){return B(A(_KI,[_KM,new T(function(){return B(A(_Kt,[_KQ,_L9,_KT]));}),_KS]));});return new F(function(){return _KV(new T(function(){return B(A(_Kn,[_KL,_L8,_L8]));}),_La,_L8);});}else{return E(_L8);}}else{_L5=new T(function(){return B(A(_Kn,[_KL,_L8,_L8]));});_L6=new T(function(){return B(A(_KI,[_KM,_L9,_KS]));});return null;}})(_L5,_L6));if(_L7!=null){return _L7;}}}else{return new F(function(){return A(_Kx,[_KL,_md]);});}}else{return E(_KH);}},_Lb=function(_Lc,_Ld){var _Le=B(_x6(_Ld)),_Lf=_Le[1],_Lg=_Le[2],_Lh=new T(function(){return B(_Hh(new T(function(){return B(_Hf(_Lc));})));});if(_Lg<0){var _Li= -_Lg;if(_Li>=0){var _Lj=E(_Li);if(!_Lj){var _Lk=E(_md);}else{var _Lk=B(_Kh(_Fv,_Lj));}if(!B(_lu(_Lk,_ot))){var _Ll=B(_ok(_Lf,_Lk));return [0,new T(function(){return B(A(_Kx,[_Lh,_Ll[1]]));}),new T(function(){return B(_og(_Ll[2],_Lg));})];}else{return E(_lt);}}else{return E(_mf);}}else{var _Lm=new T(function(){var _Ln=new T(function(){return B(_KK(_Lh,_K8,new T(function(){return B(A(_Kx,[_Lh,_Fv]));}),_Lg));});return B(A(_Kn,[_Lh,new T(function(){return B(A(_Kx,[_Lh,_Lf]));}),_Ln]));});return [0,_Lm,_pO];}},_Lo=function(_Lp){return E(E(_Lp)[1]);},_Lq=function(_Lr,_Ls){var _Lt=B(_Lb(_Lr,E(_Ls))),_Lu=_Lt[1];if(E(_Lt[2])<=0){return E(_Lu);}else{var _Lv=B(_Hh(B(_Hf(_Lr))));return new F(function(){return A(_Lo,[_Lv,_Lu,new T(function(){return B(A(_Kx,[_Lv,_o3]));})]);});}},_Lw=function(_Lx,_Ly){var _Lz=B(_Lb(_Lx,E(_Ly))),_LA=_Lz[1];if(E(_Lz[2])>=0){return E(_LA);}else{var _LB=B(_Hh(B(_Hf(_Lx))));return new F(function(){return A(_Kt,[_LB,_LA,new T(function(){return B(A(_Kx,[_LB,_o3]));})]);});}},_LC=function(_LD,_LE){var _LF=B(_Lb(_LD,E(_LE)));return [0,_LF[1],_LF[2]];},_LG=function(_LH,_LI){var _LJ=B(_Lb(_LH,_LI)),_LK=_LJ[1],_LL=E(_LJ[2]),_LM=new T(function(){var _LN=B(_Hh(B(_Hf(_LH))));if(_LL>=0){return B(A(_Lo,[_LN,_LK,new T(function(){return B(A(_Kx,[_LN,_o3]));})]));}else{return B(A(_Kt,[_LN,_LK,new T(function(){return B(A(_Kx,[_LN,_o3]));})]));}}),_LO=function(_LP){var _LQ=_LP-0.5;return (_LQ>=0)?(E(_LQ)==0)?(!B(_KB(_LH,_LK)))?E(_LM):E(_LK):E(_LM):E(_LK);},_LR=E(_LL);if(!_LR){return new F(function(){return _LO(0);});}else{if(_LR<=0){var _LS= -_LR-0.5;return (_LS>=0)?(E(_LS)==0)?(!B(_KB(_LH,_LK)))?E(_LM):E(_LK):E(_LM):E(_LK);}else{return new F(function(){return _LO(_LR);});}}},_LT=function(_LU,_LV){return new F(function(){return _LG(_LU,E(_LV));});},_LW=function(_LX,_LY){return E(B(_Lb(_LX,E(_LY)))[1]);},_LZ=[0,_He,_Eo,_LC,_LW,_LT,_Lq,_Lw],_M0=[0,_LZ,_EQ,_Fw,_Ft,_Fz,_Fh,_Fk,_Fq,_G1,_FY,_FJ,_FG,_FB,_FM,_FE,_Fe],_M1=0,_M2=1,_M3=2,_M4=1,_M5=function(_M6){return new F(function(){return err(B(unAppCStr("Char.intToDigit: not a digit ",new T(function(){if(_M6>=0){var _M7=jsShowI(_M6);return fromJSStr(_M7);}else{var _M8=jsShowI(_M6);return fromJSStr(_M8);}}))));});},_M9=function(_Ma){var _Mb=function(_Mc){if(_Ma<10){return new F(function(){return _M5(_Ma);});}else{if(_Ma>15){return new F(function(){return _M5(_Ma);});}else{return (97+_Ma|0)-10|0;}}};if(_Ma<0){return new F(function(){return _Mb(_);});}else{if(_Ma>9){return new F(function(){return _Mb(_);});}else{return 48+_Ma|0;}}},_Md=function(_Me){return new F(function(){return _M9(E(_Me));});},_Mf=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_Mg=function(_Mh){return new F(function(){return _7q([0,new T(function(){return B(_7E(_Mh,_Mf));})],_78);});},_Mi=new T(function(){return B(_Mg("GHC\\Float.hs:622:11-64|d : ds\'"));}),_Mj=0,_Mk=function(_Ml,_Mm){if(E(_Ml)<=0){var _Mn=B(_bc(_Md,[1,_Mj,_Mm]));return (_Mn[0]==0)?E(_Mi):[0,_Mn[1],_Mn[2]];}else{var _Mo=B(_bc(_Md,_Mm));return (_Mo[0]==0)?E(_Mi):[0,_Mo[1],_Mo[2]];}},_Mp=function(_Mq){return E(E(_Mq)[1]);},_Mr=function(_Ms){return E(E(_Ms)[1]);},_Mt=function(_Mu){return E(E(_Mu)[1]);},_Mv=function(_Mw){return E(E(_Mw)[1]);},_Mx=function(_My){return E(E(_My)[2]);},_Mz=46,_MA=48,_MB=new T(function(){return B(unCStr("0"));}),_MC=function(_MD,_ME,_MF){while(1){var _MG=B((function(_MH,_MI,_MJ){var _MK=E(_MH);if(!_MK){var _ML=B(_y5(_MI,_1l));if(!_ML[0]){return new F(function(){return _16(_MB,[1,_Mz,new T(function(){var _MM=E(_MJ);if(!_MM[0]){return E(_MB);}else{return E(_MM);}})]);});}else{return new F(function(){return _16(_ML,[1,_Mz,new T(function(){var _MN=E(_MJ);if(!_MN[0]){return E(_MB);}else{return E(_MN);}})]);});}}else{var _MO=E(_MJ);if(!_MO[0]){var _MP=[1,_MA,_MI];_MD=_MK-1|0;_ME=_MP;_MF=_1l;return null;}else{var _MP=[1,_MO[1],_MI];_MD=_MK-1|0;_ME=_MP;_MF=_MO[2];return null;}}})(_MD,_ME,_MF));if(_MG!=null){return _MG;}}},_MQ=function(_MR){return new F(function(){return _1g(0,E(_MR),_1l);});},_MS=function(_MT,_MU,_MV){return new F(function(){return _1g(E(_MT),E(_MU),_MV);});},_MW=function(_MX,_MY){return new F(function(){return _1g(0,E(_MX),_MY);});},_MZ=function(_N0,_N1){return new F(function(){return _6r(_MW,_N0,_N1);});},_N2=[0,_MS,_MQ,_MZ],_N3=0,_N4=function(_N5,_N6,_N7){return new F(function(){return A(_N5,[[1,_6o,new T(function(){return B(A(_N6,[_N7]));})]]);});},_N8=new T(function(){return B(unCStr(": empty list"));}),_N9=function(_Na){return new F(function(){return err(B(_16(_BR,new T(function(){return B(_16(_Na,_N8));},1))));});},_Nb=new T(function(){return B(unCStr("foldr1"));}),_Nc=new T(function(){return B(_N9(_Nb));}),_Nd=function(_Ne,_Nf){var _Ng=E(_Nf);if(!_Ng[0]){return E(_Nc);}else{var _Nh=_Ng[1],_Ni=E(_Ng[2]);if(!_Ni[0]){return E(_Nh);}else{return new F(function(){return A(_Ne,[_Nh,new T(function(){return B(_Nd(_Ne,_Ni));})]);});}}},_Nj=new T(function(){return B(unCStr(" out of range "));}),_Nk=new T(function(){return B(unCStr("}.index: Index "));}),_Nl=new T(function(){return B(unCStr("Ix{"));}),_Nm=[1,_1e,_1l],_Nn=[1,_1e,_Nm],_No=0,_Np=function(_Nq){return E(E(_Nq)[1]);},_Nr=function(_Ns,_Nt,_Nu,_Nv,_Nw){var _Nx=new T(function(){var _Ny=new T(function(){var _Nz=new T(function(){var _NA=new T(function(){var _NB=new T(function(){return B(A(_Nd,[_N4,[1,new T(function(){return B(A(_Np,[_Nu,_No,_Nv]));}),[1,new T(function(){return B(A(_Np,[_Nu,_No,_Nw]));}),_1l]],_Nn]));});return B(_16(_Nj,[1,_1f,[1,_1f,_NB]]));});return B(A(_Np,[_Nu,_N3,_Nt,[1,_1e,_NA]]));});return B(_16(_Nk,[1,_1f,_Nz]));},1);return B(_16(_Ns,_Ny));},1);return new F(function(){return err(B(_16(_Nl,_Nx)));});},_NC=function(_ND,_NE,_NF,_NG,_NH){return new F(function(){return _Nr(_ND,_NE,_NH,_NF,_NG);});},_NI=function(_NJ,_NK,_NL,_NM){var _NN=E(_NL);return new F(function(){return _NC(_NJ,_NK,_NN[1],_NN[2],_NM);});},_NO=function(_NP,_NQ,_NR,_NS){return new F(function(){return _NI(_NS,_NR,_NQ,_NP);});},_NT=new T(function(){return B(unCStr("Int"));}),_NU=function(_NV,_NW,_NX){return new F(function(){return _NO(_N2,[0,_NW,_NX],_NV,_NT);});},_NY=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_NZ=new T(function(){return B(err(_NY));}),_O0=1100,_O1=[0,_Mj,_O0],_O2=function(_O3){return new F(function(){return _NO(_N2,_O1,_O3,_NT);});},_O4=function(_){var _O5=newArr(1101,_NZ),_O6=_O5,_O7=0;while(1){var _O8=B((function(_O9,_){if(0>_O9){return new F(function(){return _O2(_O9);});}else{if(_O9>1100){return new F(function(){return _O2(_O9);});}else{var _=_O6[_O9]=new T(function(){if(_O9>=0){var _Oa=E(_O9);if(!_Oa){return E(_md);}else{return B(_Kh(_Fv,_Oa));}}else{return E(_mf);}}),_Ob=E(_O9);if(_Ob==1100){return [0,E(_Mj),E(_O0),1101,_O6];}else{_O7=_Ob+1|0;return null;}}}})(_O7,_));if(_O8!=null){return _O8;}}},_Oc=function(_Od){var _Oe=B(A(_Od,[_]));return E(_Oe);},_Of=new T(function(){return B(_Oc(_O4));}),_Og=[0,10],_Oh=324,_Oi=[0,_Mj,_Oh],_Oj=function(_Ok){return new F(function(){return _NO(_N2,_Oi,_Ok,_NT);});},_Ol=function(_){var _Om=newArr(325,_NZ),_On=_Om,_Oo=0;while(1){var _Op=B((function(_Oq,_){if(0>_Oq){return new F(function(){return _Oj(_Oq);});}else{if(_Oq>324){return new F(function(){return _Oj(_Oq);});}else{var _=_On[_Oq]=new T(function(){if(_Oq>=0){var _Or=E(_Oq);if(!_Or){return E(_md);}else{return B(_Kh(_Og,_Or));}}else{return E(_mf);}}),_Os=E(_Oq);if(_Os==324){return [0,E(_Mj),E(_Oh),325,_On];}else{_Oo=_Os+1|0;return null;}}}})(_Oo,_));if(_Op!=null){return _Op;}}},_Ot=new T(function(){return B(_Oc(_Ol));}),_Ou=function(_Ov,_Ow){var _Ox=function(_Oy){if(!B(_lu(_Ov,_Og))){if(_Ow>=0){var _Oz=E(_Ow);if(!_Oz){return E(_md);}else{return new F(function(){return _Kh(_Ov,_Oz);});}}else{return E(_mf);}}else{if(_Ow>324){if(_Ow>=0){var _OA=E(_Ow);if(!_OA){return E(_md);}else{return new F(function(){return _Kh(_Ov,_OA);});}}else{return E(_mf);}}else{var _OB=E(_Ot),_OC=E(_OB[1]),_OD=E(_OB[2]);if(_OC>_Ow){return new F(function(){return _NU(_Ow,_OC,_OD);});}else{if(_Ow>_OD){return new F(function(){return _NU(_Ow,_OC,_OD);});}else{return E(_OB[4][_Ow-_OC|0]);}}}}};if(!B(_lu(_Ov,_Fv))){return new F(function(){return _Ox(_);});}else{if(_Ow<0){return new F(function(){return _Ox(_);});}else{if(_Ow>1100){return new F(function(){return _Ox(_);});}else{var _OE=E(_Of),_OF=E(_OE[1]),_OG=E(_OE[2]);if(_OF>_Ow){return new F(function(){return _NU(_Ow,_OF,_OG);});}else{if(_Ow>_OG){return new F(function(){return _NU(_Ow,_OF,_OG);});}else{return E(_OE[4][_Ow-_OF|0]);}}}}}},_OH=function(_OI){return E(E(_OI)[6]);},_OJ=function(_OK){return E(E(_OK)[4]);},_OL=function(_OM){var _ON=E(_OM);if(!_ON[0]){return _ON[1];}else{return new F(function(){return I_toNumber(_ON[1]);});}},_OO=function(_OP){return E(E(_OP)[3]);},_OQ=function(_OR){return E(E(_OR)[5]);},_OS=[1,_Mj,_1l],_OT=function(_OU,_OV,_OW){if(!B(A(_T,[B(_Kp(B(_Kr(B(_Mv(B(_Mt(_OU)))))))),_OW,new T(function(){return B(A(_Kx,[B(_Mr(B(_Mp(B(_Mx(_OU)))))),_ot]));})]))){var _OX=new T(function(){return B(A(_OO,[_OU,_OW]));}),_OY=new T(function(){return B(A(_OJ,[_OU,_OW]));}),_OZ=new T(function(){return E(B(A(_OQ,[_OU,_OW]))[1])-E(_OY)|0;}),_P0=new T(function(){return B(A(_OH,[_OU,_OW]));}),_P1=new T(function(){return E(E(_P0)[2]);}),_P2=new T(function(){var _P3=E(_P1),_P4=E(_OZ)-_P3|0;if(_P4<=0){return [0,new T(function(){return E(E(_P0)[1]);}),_P3];}else{return [0,new T(function(){var _P5=B(_Ou(_OX,_P4));if(!B(_lu(_P5,_ot))){return B(_lY(E(_P0)[1],_P5));}else{return E(_lt);}}),_P3+_P4|0];}}),_P6=new T(function(){return E(E(_P2)[2]);}),_P7=new T(function(){return E(E(_P2)[1]);}),_P8=new T(function(){var _P9=E(_P6);if(_P9<0){if(_P9<=E(_OZ)){return [0,new T(function(){return B(_bm(_P7,_Fv));}),new T(function(){return B(_bm(B(_Ou(_OX, -_P9)),_Fv));}),_o3,_o3];}else{if(!B(_lu(_P7,B(_Ou(_OX,E(_OY)-1|0))))){return [0,new T(function(){return B(_bm(_P7,_Fv));}),new T(function(){return B(_bm(B(_Ou(_OX, -_P9)),_Fv));}),_o3,_o3];}else{return [0,new T(function(){return B(_bm(B(_bm(_P7,_OX)),_Fv));}),new T(function(){return B(_bm(B(_Ou(_OX, -_P9+1|0)),_Fv));}),_OX,_o3];}}}else{var _Pa=new T(function(){return B(_Ou(_OX,_P9));});if(!B(_lu(_P7,B(_Ou(_OX,E(_OY)-1|0))))){return [0,new T(function(){return B(_bm(B(_bm(_P7,_Pa)),_Fv));}),_Fv,_Pa,_Pa];}else{return [0,new T(function(){return B(_bm(B(_bm(B(_bm(_P7,_Pa)),_OX)),_Fv));}),new T(function(){return B(_bm(_Fv,_OX));}),new T(function(){return B(_bm(_Pa,_OX));}),_Pa];}}}),_Pb=new T(function(){return E(E(_P8)[2]);}),_Pc=new T(function(){return E(E(_P8)[3]);}),_Pd=new T(function(){return E(E(_P8)[1]);}),_Pe=new T(function(){var _Pf=new T(function(){return B(_aS(_Pd,_Pc));}),_Pg=function(_Ph){var _Pi=(Math.log(B(_OL(B(_aS(_P7,_o3)))))+E(_P6)*Math.log(B(_OL(_OX))))/Math.log(B(_OL(_OV))),_Pj=_Pi&4294967295;return (_Pj>=_Pi)?E(_Pj):_Pj+1|0;},_Pk=function(_Pl){while(1){if(_Pl<0){if(!B(_cN(B(_bm(B(_Ou(_OV, -_Pl)),_Pf)),_Pb))){var _Pm=_Pl+1|0;_Pl=_Pm;continue;}else{return E(_Pl);}}else{if(!B(_cN(_Pf,B(_bm(B(_Ou(_OV,_Pl)),_Pb))))){var _Pm=_Pl+1|0;_Pl=_Pm;continue;}else{return E(_Pl);}}}};if(!B(_lu(_OX,_Fv))){return B(_Pk(B(_Pg(_))));}else{if(!B(_lu(_OV,_Og))){return B(_Pk(B(_Pg(_))));}else{var _Pn=(E(_OY)-1|0)+E(_P1)|0;if(_Pn<0){return B(_Pk(quot(imul(_Pn,8651)|0,28738)));}else{return B(_Pk(quot(imul(_Pn,8651)|0,28738)+1|0));}}}}),_Po=new T(function(){var _Pp=E(_Pe),_Pq=function(_Pr,_Ps,_Pt,_Pu,_Pv){while(1){var _Pw=B((function(_Px,_Py,_Pz,_PA,_PB){if(!B(_lu(_Pz,_ot))){var _PC=B(_ok(B(_bm(_Py,_OV)),_Pz)),_PD=_PC[1],_PE=_PC[2],_PF=B(_bm(_PB,_OV)),_PG=B(_bm(_PA,_OV));if(!B(_mD(_PE,_PF))){if(!B(_ns(B(_aS(_PE,_PG)),_Pz))){var _PH=[1,_PD,_Px],_PI=_Pz;_Pr=_PH;_Ps=_PE;_Pt=_PI;_Pu=_PG;_Pv=_PF;return null;}else{return [1,new T(function(){return B(_aS(_PD,_o3));}),_Px];}}else{return (!B(_ns(B(_aS(_PE,_PG)),_Pz)))?[1,_PD,_Px]:(!B(_mD(B(_bm(_PE,_Fv)),_Pz)))?[1,new T(function(){return B(_aS(_PD,_o3));}),_Px]:[1,_PD,_Px];}}else{return E(_lt);}})(_Pr,_Ps,_Pt,_Pu,_Pv));if(_Pw!=null){return _Pw;}}};if(_Pp<0){var _PJ=B(_Ou(_OV, -_Pp));return B(_bc(_Jp,B(_y5(B(_Pq(_1l,B(_bm(_Pd,_PJ)),_Pb,B(_bm(_Pc,_PJ)),B(_bm(E(_P8)[4],_PJ)))),_1l))));}else{return B(_bc(_Jp,B(_y5(B(_Pq(_1l,_Pd,B(_bm(_Pb,B(_Ou(_OV,_Pp)))),_Pc,E(_P8)[4])),_1l))));}});return [0,_Po,_Pe];}else{return [0,_OS,_Mj];}},_PK=function(_PL){var _PM=E(_PL);return (_PM==1)?E(_OS):[1,_Mj,new T(function(){return B(_PK(_PM-1|0));})];},_PN=function(_PO,_PP){while(1){var _PQ=E(_PP);if(!_PQ[0]){return true;}else{if(!B(A(_PO,[_PQ[1]]))){return false;}else{_PP=_PQ[2];continue;}}}},_PR=function(_PS){return (E(_PS)%2==0)?true:false;},_PT=new T(function(){return B(unCStr("roundTo: bad Value"));}),_PU=new T(function(){return B(err(_PT));}),_PV=function(_PW){return (E(_PW)==0)?true:false;},_PX=function(_PY,_PZ,_Q0){var _Q1=new T(function(){return quot(E(_PY),2);}),_Q2=function(_Q3,_Q4,_Q5){var _Q6=E(_Q5);if(!_Q6[0]){return [0,_Mj,new T(function(){var _Q7=E(_Q3);if(0>=_Q7){return [0];}else{return B(_PK(_Q7));}})];}else{var _Q8=_Q6[1],_Q9=_Q6[2],_Qa=E(_Q3);if(!_Qa){var _Qb=E(_Q8),_Qc=E(_Q1);return (_Qb!=_Qc)?[0,new T(function(){if(_Qb<_Qc){return E(_Mj);}else{return E(_M4);}}),_1l]:(!E(_Q4))?[0,new T(function(){if(_Qb<_Qc){return E(_Mj);}else{return E(_M4);}}),_1l]:(!B(_PN(_PV,_Q9)))?[0,new T(function(){if(_Qb<_Qc){return E(_Mj);}else{return E(_M4);}}),_1l]:[0,_Mj,_1l];}else{var _Qd=B(_Q2(_Qa-1|0,new T(function(){return B(_PR(_Q8));},1),_Q9)),_Qe=_Qd[2],_Qf=E(_Qd[1])+E(_Q8)|0;return (_Qf!=E(_PY))?[0,_Mj,[1,_Qf,_Qe]]:[0,_M4,[1,_Mj,_Qe]];}}},_Qg=B(_Q2(_PZ,_cy,_Q0)),_Qh=_Qg[1],_Qi=_Qg[2];switch(E(_Qh)){case 0:return [0,_Qh,_Qi];case 1:return [0,_M4,[1,_M4,_Qi]];default:return E(_PU);}},_Qj=function(_Qk,_Ql){var _Qm=E(_Ql);if(!_Qm[0]){return [0,_1l,_1l];}else{var _Qn=_Qm[1],_Qo=_Qm[2],_Qp=E(_Qk);if(_Qp==1){return [0,[1,_Qn,_1l],_Qo];}else{var _Qq=new T(function(){var _Qr=B(_Qj(_Qp-1|0,_Qo));return [0,_Qr[1],_Qr[2]];});return [0,[1,_Qn,new T(function(){return E(E(_Qq)[1]);})],new T(function(){return E(E(_Qq)[2]);})];}}},_Qs=new T(function(){return B(unCStr("e0"));}),_Qt=[1,_MA,_Qs],_Qu=function(_Qv){var _Qw=E(_Qv);return (_Qw==1)?E(_Qt):[1,_MA,new T(function(){return B(_Qu(_Qw-1|0));})];},_Qx=10,_Qy=function(_Qz,_QA){var _QB=E(_QA);return (_QB[0]==0)?[0]:[1,_Qz,new T(function(){return B(_Qy(_QB[1],_QB[2]));})];},_QC=new T(function(){return B(unCStr("init"));}),_QD=new T(function(){return B(_N9(_QC));}),_QE=function(_QF){return E(E(_QF)[12]);},_QG=function(_QH){return E(E(_QH)[11]);},_QI=function(_QJ){return E(E(_QJ)[14]);},_QK=new T(function(){return B(unCStr("NaN"));}),_QL=new T(function(){return B(unCStr("-Infinity"));}),_QM=new T(function(){return B(unCStr("formatRealFloat/doFmt/FFExponent: []"));}),_QN=new T(function(){return B(err(_QM));}),_QO=new T(function(){return B(unCStr("Infinity"));}),_QP=[1,_Mz,_1l],_QQ=101,_QR=new T(function(){return B(_Mg("GHC\\Float.hs:594:12-70|(d : ds\')"));}),_QS=new T(function(){return B(unCStr("0.0e0"));}),_QT=function(_QU){return E(E(_QU)[4]);},_QV=45,_QW=function(_QX,_QY,_QZ,_R0,_R1){if(!B(A(_QG,[_QX,_R1]))){var _R2=new T(function(){return B(_Mr(new T(function(){return B(_Mp(new T(function(){return B(_Mx(_QX));})));})));});if(!B(A(_QE,[_QX,_R1]))){var _R3=function(_R4,_R5,_R6){while(1){var _R7=B((function(_R8,_R9,_Ra){switch(E(_R8)){case 0:var _Rb=E(_QZ);if(!_Rb[0]){var _Rc=B(_bc(_Md,_R9));if(!_Rc[0]){return E(_QN);}else{var _Rd=_Rc[2],_Re=E(_Rc[1]),_Rf=function(_Rg){var _Rh=E(_Rd);if(!_Rh[0]){var _Ri=new T(function(){return B(unAppCStr(".0e",new T(function(){return B(_1g(0,E(_Ra)-1|0,_1l));})));});return [1,_Re,_Ri];}else{var _Rj=new T(function(){var _Rk=new T(function(){return B(unAppCStr("e",new T(function(){return B(_1g(0,E(_Ra)-1|0,_1l));})));},1);return B(_16(_Rh,_Rk));});return [1,_Re,[1,_Mz,_Rj]];}};if(E(_Re)==48){if(!E(_Rd)[0]){return E(_QS);}else{return new F(function(){return _Rf(_);});}}else{return new F(function(){return _Rf(_);});}}}else{var _Rl=new T(function(){var _Rm=E(_Rb[1]);if(_Rm>1){return E(_Rm);}else{return E(_M4);}}),_Rn=function(_Ro){var _Rp=new T(function(){var _Rq=B(_PX(_Qx,new T(function(){return E(_Rl)+1|0;},1),_R9));return [0,_Rq[1],_Rq[2]];}),_Rr=new T(function(){return E(E(_Rp)[1]);}),_Rs=new T(function(){if(E(_Rr)<=0){var _Rt=B(_bc(_Md,E(_Rp)[2]));if(!_Rt[0]){return E(_QR);}else{return [0,_Rt[1],_Rt[2]];}}else{var _Ru=E(E(_Rp)[2]);if(!_Ru[0]){return E(_QD);}else{var _Rv=B(_bc(_Md,B(_Qy(_Ru[1],_Ru[2]))));if(!_Rv[0]){return E(_QR);}else{return [0,_Rv[1],_Rv[2]];}}}}),_Rw=new T(function(){return B(_16(E(_Rs)[2],[1,_QQ,new T(function(){return B(_1g(0,(E(_Ra)-1|0)+E(_Rr)|0,_1l));})]));});return [1,new T(function(){return E(E(_Rs)[1]);}),[1,_Mz,_Rw]];},_Rx=E(_R9);if(!_Rx[0]){return new F(function(){return _Rn(_);});}else{if(!E(_Rx[1])){if(!E(_Rx[2])[0]){return [1,_MA,[1,_Mz,new T(function(){var _Ry=E(_Rl);if(0>=_Ry){return E(_Qs);}else{return B(_Qu(_Ry));}})]];}else{return new F(function(){return _Rn(_);});}}else{return new F(function(){return _Rn(_);});}}}break;case 1:var _Rz=E(_QZ);if(!_Rz[0]){var _RA=E(_Ra);if(_RA>0){return new F(function(){return _MC(_RA,_1l,new T(function(){return B(_bc(_Md,_R9));},1));});}else{var _RB=new T(function(){var _RC= -_RA;if(0>=_RC){return B(_bc(_Md,_R9));}else{var _RD=new T(function(){return B(_bc(_Md,_R9));}),_RE=function(_RF){var _RG=E(_RF);return (_RG==1)?[1,_MA,_RD]:[1,_MA,new T(function(){return B(_RE(_RG-1|0));})];};return B(_RE(_RC));}});return new F(function(){return unAppCStr("0.",_RB);});}}else{var _RH=_Rz[1],_RI=E(_Ra);if(_RI<0){var _RJ=new T(function(){var _RK= -_RI;if(0>=_RK){var _RL=B(_PX(_Qx,new T(function(){var _RM=E(_RH);if(_RM>0){return E(_RM);}else{return E(_Mj);}},1),_R9));return B(_Mk(_RL[1],_RL[2]));}else{var _RN=function(_RO){var _RP=E(_RO);return (_RP==1)?[1,_Mj,_R9]:[1,_Mj,new T(function(){return B(_RN(_RP-1|0));})];},_RQ=B(_PX(_Qx,new T(function(){var _RR=E(_RH);if(_RR>0){return E(_RR);}else{return E(_Mj);}},1),B(_RN(_RK))));return B(_Mk(_RQ[1],_RQ[2]));}});return [1,new T(function(){return E(E(_RJ)[1]);}),new T(function(){var _RS=E(E(_RJ)[2]);if(!_RS[0]){if(!E(_R0)){return [0];}else{return E(_QP);}}else{return [1,_Mz,_RS];}})];}else{var _RT=B(_PX(_Qx,new T(function(){var _RU=E(_RH);if(_RU>0){return _RU+_RI|0;}else{return E(_RI);}},1),_R9)),_RV=_RT[2],_RW=_RI+E(_RT[1])|0;if(_RW>0){var _RX=B(_Qj(_RW,B(_bc(_Md,_RV)))),_RY=_RX[2],_RZ=E(_RX[1]);if(!_RZ[0]){return new F(function(){return _16(_MB,new T(function(){var _S0=E(_RY);if(!_S0[0]){if(!E(_R0)){return [0];}else{return E(_QP);}}else{return [1,_Mz,_S0];}},1));});}else{return new F(function(){return _16(_RZ,new T(function(){var _S1=E(_RY);if(!_S1[0]){if(!E(_R0)){return [0];}else{return E(_QP);}}else{return [1,_Mz,_S1];}},1));});}}else{return new F(function(){return _16(_MB,new T(function(){var _S2=B(_bc(_Md,_RV));if(!_S2[0]){if(!E(_R0)){return [0];}else{return E(_QP);}}else{return [1,_Mz,_S2];}},1));});}}}break;default:var _S3=E(_Ra);if(_S3>=0){if(_S3<=7){var _S4=_R9;_R4=_M2;_R5=_S4;_R6=_S3;return null;}else{var _S4=_R9;_R4=_M1;_R5=_S4;_R6=_S3;return null;}}else{var _S4=_R9;_R4=_M1;_R5=_S4;_R6=_S3;return null;}}})(_R4,_R5,_R6));if(_R7!=null){return _R7;}}},_S5=function(_S6){var _S7=new T(function(){var _S8=B(_OT(_QX,_Og,new T(function(){return B(A(_QT,[_R2,_R1]));})));return B(_R3(_QY,_S8[1],_S8[2]));});return [1,_QV,_S7];};if(!B(A(_Kv,[B(_Kr(B(_Mv(B(_Mt(_QX)))))),_R1,new T(function(){return B(A(_Kx,[_R2,_ot]));})]))){if(!B(A(_QI,[_QX,_R1]))){var _S9=B(_OT(_QX,_Og,_R1));return new F(function(){return _R3(_QY,_S9[1],_S9[2]);});}else{return new F(function(){return _S5(_);});}}else{return new F(function(){return _S5(_);});}}else{return (!B(A(_Kv,[B(_Kr(B(_Mv(B(_Mt(_QX)))))),_R1,new T(function(){return B(A(_Kx,[_R2,_ot]));})])))?E(_QO):E(_QL);}}else{return E(_QK);}},_Sa=function(_Sb){var _Sc=u_towupper(E(_Sb));if(_Sc>>>0>1114111){return new F(function(){return _cI(_Sc);});}else{return _Sc;}},_Sd=function(_Se,_Sf,_Sg,_Sh){var _Si=u_iswupper(_Se),_Sj=_Si,_Sk=u_towlower(_Se);if(_Sk>>>0>1114111){var _Sl=B(_cI(_Sk));}else{switch(_Sk){case 101:var _Sm=B(_QW(_M0,_M1,_Sf,_cx,_Sh));break;case 102:if(!E(_Sg)){var _Sn=B(_QW(_M0,_M2,_Sf,_cx,_Sh));}else{var _Sn=B(_QW(_M0,_M2,_Sf,_cy,_Sh));}var _Sm=_Sn;break;case 103:if(!E(_Sg)){var _So=B(_QW(_M0,_M3,_Sf,_cx,_Sh));}else{var _So=B(_QW(_M0,_M3,_Sf,_cy,_Sh));}var _Sm=_So;break;default:var _Sm=E(_DF);}var _Sl=_Sm;}if(!E(_Sj)){var _Sp=E(_Sl);return (_Sp[0]==0)?[0,_1l,_1l]:(E(_Sp[1])==45)?[0,_DD,_Sp[2]]:[0,_1l,_Sp];}else{var _Sq=B(_bc(_Sa,_Sl));return (_Sq[0]==0)?[0,_1l,_1l]:(E(_Sq[1])==45)?[0,_DD,_Sq[2]]:[0,_1l,_Sq];}},_Sr=new T(function(){return B(unCStr(" "));}),_Ss=new T(function(){return B(unCStr("+"));}),_St=48,_Su=32,_Sv=function(_Sw,_Sx,_Sy,_Sz){var _SA=new T(function(){var _SB=E(_Sx);if(!_SB[0]){return false;}else{if(!E(_SB[1])){return false;}else{return true;}}}),_SC=new T(function(){var _SD=E(_Sw);if(!_SD[0]){return [0];}else{var _SE=E(_SD[1]),_SF=B(_b7(_Sy,0))+B(_b7(_Sz,0))|0;if(_SF>=_SE){return [0];}else{var _SG=_SE-_SF|0;if(0>=_SG){return [0];}else{var _SH=new T(function(){if(!E(_SA)){return E(_Su);}else{return E(_St);}}),_SI=function(_SJ){var _SK=E(_SJ);return (_SK==1)?[1,_SH,_1l]:[1,_SH,new T(function(){return B(_SI(_SK-1|0));})];};return B(_SI(_SG));}}}}),_SL=function(_SM){if(!E(_SA)){return new F(function(){return _16(_SC,new T(function(){return B(_16(_Sy,_Sz));},1));});}else{return new F(function(){return _16(_Sy,new T(function(){return B(_16(_SC,_Sz));},1));});}},_SN=E(_Sx);if(!_SN[0]){return new F(function(){return _SL(_);});}else{if(!E(_SN[1])){return new F(function(){return _16(_Sy,new T(function(){return B(_16(_Sz,_SC));},1));});}else{return new F(function(){return _SL(_);});}}},_SO=function(_SP,_SQ,_SR,_SS,_ST){var _SU=E(_SR);if(!_SU[0]){return new F(function(){return _Sv(_SP,_SQ,_SS,_ST);});}else{if(!E(_SU[1])){var _SV=E(_SS);if(!_SV[0]){return new F(function(){return _Sv(_SP,_SQ,_Ss,_ST);});}else{return new F(function(){return _Sv(_SP,_SQ,_SV,_ST);});}}else{var _SW=E(_SS);if(!_SW[0]){return new F(function(){return _Sv(_SP,_SQ,_Sr,_ST);});}else{return new F(function(){return _Sv(_SP,_SQ,_SW,_ST);});}}}},_SX=function(_SY,_SZ,_T0,_T1,_T2,_T3,_T4){var _T5=E(_T4);switch(_T5){case 69:var _T6=new T(function(){var _T7=B(_Sd(69,_T0,_T3,_SY));return B(_SO(_SZ,_T1,_T2,_T7[1],_T7[2]));});return function(_qJ){return new F(function(){return _16(_T6,_qJ);});};case 70:var _T8=new T(function(){var _T9=B(_Sd(70,_T0,_T3,_SY));return B(_SO(_SZ,_T1,_T2,_T9[1],_T9[2]));});return function(_qJ){return new F(function(){return _16(_T8,_qJ);});};case 71:var _Ta=new T(function(){var _Tb=B(_Sd(71,_T0,_T3,_SY));return B(_SO(_SZ,_T1,_T2,_Tb[1],_Tb[2]));});return function(_qJ){return new F(function(){return _16(_Ta,_qJ);});};case 101:var _Tc=new T(function(){var _Td=B(_Sd(101,_T0,_T3,_SY));return B(_SO(_SZ,_T1,_T2,_Td[1],_Td[2]));});return function(_qJ){return new F(function(){return _16(_Tc,_qJ);});};case 102:var _Te=new T(function(){var _Tf=B(_Sd(102,_T0,_T3,_SY));return B(_SO(_SZ,_T1,_T2,_Tf[1],_Tf[2]));});return function(_qJ){return new F(function(){return _16(_Te,_qJ);});};case 103:var _Tg=new T(function(){var _Th=B(_Sd(103,_T0,_T3,_SY));return B(_SO(_SZ,_T1,_T2,_Th[1],_Th[2]));});return function(_qJ){return new F(function(){return _16(_Tg,_qJ);});};case 118:var _Ti=new T(function(){var _Tj=B(_Sd(103,_T0,_T3,_SY));return B(_SO(_SZ,_T1,_T2,_Tj[1],_Tj[2]));});return function(_qJ){return new F(function(){return _16(_Ti,_qJ);});};default:return new F(function(){return _Dy(_T5);});}},_Tk=function(_Tl,_Tm){var _Tn=E(_Tm);return new F(function(){return _SX(_Tl,_Tn[1],_Tn[2],_Tn[3],_Tn[4],_Tn[5],E(_Tn[7]));});},_To=function(_Tp){return E(_Tp);},_Tq=new T(function(){return B(unCStr("printf: argument list ended prematurely"));}),_Tr=new T(function(){return B(err(_Tq));}),_Ts=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_Tt=new T(function(){return B(err(_Ts));}),_Tu=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_Tv=new T(function(){return B(err(_Tu));}),_Tw=function(_Tx,_Ty){var _Tz=function(_TA,_TB){var _TC=function(_TD){return new F(function(){return A(_TB,[new T(function(){return  -E(_TD);})]);});},_TE=new T(function(){return B(_jm(function(_TF){return new F(function(){return A(_Tx,[_TF,_TA,_TC]);});}));}),_TG=function(_TH){return E(_TE);},_TI=function(_TJ){return new F(function(){return A(_i3,[_TJ,_TG]);});},_TK=new T(function(){return B(_jm(function(_TL){var _TM=E(_TL);if(_TM[0]==4){var _TN=E(_TM[1]);if(!_TN[0]){return new F(function(){return A(_Tx,[_TM,_TA,_TB]);});}else{if(E(_TN[1])==45){if(!E(_TN[2])[0]){return [1,_TI];}else{return new F(function(){return A(_Tx,[_TM,_TA,_TB]);});}}else{return new F(function(){return A(_Tx,[_TM,_TA,_TB]);});}}}else{return new F(function(){return A(_Tx,[_TM,_TA,_TB]);});}}));}),_TO=function(_TP){return E(_TK);};return [1,function(_TQ){return new F(function(){return A(_i3,[_TQ,_TO]);});}];};return new F(function(){return _kd(_Tz,_Ty);});},_TR=function(_TS){var _TT=E(_TS);if(!_TT[0]){var _TU=_TT[2];return [1,new T(function(){return B(_bA(new T(function(){return B(_bg(E(_TT[1])));}),new T(function(){return B(_b7(_TU,0));},1),B(_bc(_bi,_TU))));})];}else{return (E(_TT[2])[0]==0)?(E(_TT[3])[0]==0)?[1,new T(function(){return B(_bQ(_b6,_TT[1]));})]:[0]:[0];}},_TV=function(_TW){var _TX=E(_TW);if(_TX[0]==5){var _TY=B(_TR(_TX[1]));if(!_TY[0]){return E(_o0);}else{var _TZ=new T(function(){return B(_cK(_TY[1]));});return function(_U0,_U1){return new F(function(){return A(_U1,[_TZ]);});};}}else{return E(_o0);}},_U2=function(_U3){var _U4=function(_U5){return [3,_U3,_8Y];};return [1,function(_U6){return new F(function(){return A(_i3,[_U6,_U4]);});}];},_U7=new T(function(){return B(A(_Tw,[_TV,_jT,_U2]));}),_U8=100,_U9=[0,_6J,_6J,_6J,_6J,_cx,_1l,_U8],_Ua=function(_Ub){while(1){var _Uc=B((function(_Ud){var _Ue=E(_Ud);if(!_Ue[0]){return [0];}else{var _Uf=_Ue[2],_Ug=E(_Ue[1]);if(!E(_Ug[2])[0]){return [1,_Ug[1],new T(function(){return B(_Ua(_Uf));})];}else{_Ub=_Uf;return null;}}})(_Ub));if(_Uc!=null){return _Uc;}}},_Uh=function(_Ui){var _Uj=E(_Ui);if(!_Uj[0]){return E(_Tr);}else{var _Uk=new T(function(){var _Ul=B(_Ua(B(_7S(_U7,new T(function(){return B(A(E(_Uj[1])[2],[_U9,_1l]));})))));if(!_Ul[0]){return E(_Tt);}else{if(!E(_Ul[2])[0]){return E(_Ul[1]);}else{return E(_Tv);}}});return [0,_Uj[2],_Uk];}},_Um=function(_Un){return (E(_Un)-48|0)>>>0<=9;},_Uo=0,_Up=[1,_Uo],_Uq=0,_Ur=0,_Us=[1,_Ur],_Ut=1,_Uu=[1,_Ut],_Uv=new T(function(){var _Uw=B(_7t(_Um,_1l)),_Ux=_Uw[2],_Uy=E(_Uw[1]);if(!_Uy[0]){return [0,_Uq,_Ux];}else{return [0,new T(function(){var _Uz=B(_Ua(B(_7S(_U7,_Uy))));if(!_Uz[0]){return E(_Tt);}else{if(!E(_Uz[2])[0]){return E(_Uz[1]);}else{return E(_Tv);}}}),_Ux];}}),_UA=new T(function(){return E(E(_Uv)[1]);}),_UB=[1,_UA],_UC=new T(function(){return E(E(_Uv)[2]);}),_UD=1,_UE=[1,_UD],_UF=function(_UG,_UH,_UI,_UJ,_UK,_UL){while(1){var _UM=B((function(_UN,_UO,_UP,_UQ,_UR,_US){var _UT=E(_UR);if(!_UT[0]){return E(_BL);}else{var _UU=_UT[2],_UV=E(_UT[1]);switch(_UV){case 32:var _UW=_UN,_UX=_UO,_UY=_UQ,_UZ=_US;_UG=_UW;_UH=_UX;_UI=new T(function(){var _V0=E(_UP);if(!_V0[0]){return E(_Uu);}else{if(!E(_V0[1])){return E(_Us);}else{return E(_Uu);}}});_UJ=_UY;_UK=_UU;_UL=_UZ;return null;case 35:var _UW=_UN,_UX=_UO,_V1=_UP,_UZ=_US;_UG=_UW;_UH=_UX;_UI=_V1;_UJ=_cy;_UK=_UU;_UL=_UZ;return null;case 42:var _V2=new T(function(){var _V3=B(_Uh(_US));return [0,_V3[1],_V3[2]];}),_V4=new T(function(){var _V5=E(_UU);if(!_V5[0]){return [0,_6J,_1l,new T(function(){return E(E(_V2)[1]);})];}else{if(E(_V5[1])==46){var _V6=E(_V5[2]);if(!_V6[0]){return [0,_UB,_UC,new T(function(){return E(E(_V2)[1]);})];}else{if(E(_V6[1])==42){var _V7=new T(function(){var _V8=B(_Uh(E(_V2)[1]));return [0,_V8[1],_V8[2]];});return [0,[1,new T(function(){return E(E(_V7)[2]);})],_V6[2],new T(function(){return E(E(_V7)[1]);})];}else{var _V9=new T(function(){var _Va=B(_7t(_Um,_V6)),_Vb=_Va[2],_Vc=E(_Va[1]);if(!_Vc[0]){return [0,_Uq,_Vb];}else{return [0,new T(function(){var _Vd=B(_Ua(B(_7S(_U7,_Vc))));if(!_Vd[0]){return E(_Tt);}else{if(!E(_Vd[2])[0]){return E(_Vd[1]);}else{return E(_Tv);}}}),_Vb];}});return [0,[1,new T(function(){return E(E(_V9)[1]);})],new T(function(){return E(E(_V9)[2]);}),new T(function(){return E(E(_V2)[1]);})];}}}else{return [0,_6J,_V5,new T(function(){return E(E(_V2)[1]);})];}}}),_Ve=new T(function(){return E(E(_V4)[3]);}),_Vf=new T(function(){var _Vg=E(_Ve);if(!_Vg[0]){return E(_Tr);}else{return B(A(E(_Vg[1])[1],[new T(function(){return E(E(_V4)[2]);})]));}}),_Vh=new T(function(){return E(E(_V2)[2]);});return [0,[0,[1,new T(function(){return B(_Jm(_Vh));})],new T(function(){return E(E(_V4)[1]);}),new T(function(){if(E(_Vh)>=0){if(!E(_UN)){if(!E(_UO)){return [0];}else{return E(_UE);}}else{return E(_Up);}}else{return E(_Up);}}),_UP,_UQ,new T(function(){return E(E(_Vf)[1]);}),new T(function(){return E(E(_Vf)[2]);})],new T(function(){return E(E(_Vf)[3]);}),_Ve];case 43:var _UW=_UN,_UX=_UO,_UY=_UQ,_UZ=_US;_UG=_UW;_UH=_UX;_UI=_Us;_UJ=_UY;_UK=_UU;_UL=_UZ;return null;case 45:var _UX=_UO,_V1=_UP,_UY=_UQ,_UZ=_US;_UG=_cy;_UH=_UX;_UI=_V1;_UJ=_UY;_UK=_UU;_UL=_UZ;return null;case 46:var _Vi=new T(function(){var _Vj=E(_UU);if(!_Vj[0]){var _Vk=B(_7t(_Um,_1l)),_Vl=_Vk[2],_Vm=E(_Vk[1]);if(!_Vm[0]){return [0,_Uq,_Vl,_US];}else{return [0,new T(function(){var _Vn=B(_Ua(B(_7S(_U7,_Vm))));if(!_Vn[0]){return E(_Tt);}else{if(!E(_Vn[2])[0]){return E(_Vn[1]);}else{return E(_Tv);}}}),_Vl,_US];}}else{if(E(_Vj[1])==42){var _Vo=new T(function(){var _Vp=B(_Uh(_US));return [0,_Vp[1],_Vp[2]];});return [0,new T(function(){return E(E(_Vo)[2]);}),_Vj[2],new T(function(){return E(E(_Vo)[1]);})];}else{var _Vq=B(_7t(_Um,_Vj)),_Vr=_Vq[2],_Vs=E(_Vq[1]);if(!_Vs[0]){return [0,_Uq,_Vr,_US];}else{return [0,new T(function(){var _Vt=B(_Ua(B(_7S(_U7,_Vs))));if(!_Vt[0]){return E(_Tt);}else{if(!E(_Vt[2])[0]){return E(_Vt[1]);}else{return E(_Tv);}}}),_Vr,_US];}}}}),_Vu=new T(function(){return E(E(_Vi)[3]);}),_Vv=new T(function(){var _Vw=E(_Vu);if(!_Vw[0]){return E(_Tr);}else{return B(A(E(_Vw[1])[1],[new T(function(){return E(E(_Vi)[2]);})]));}});return [0,[0,_6J,[1,new T(function(){return E(E(_Vi)[1]);})],new T(function(){if(!E(_UN)){if(!E(_UO)){return [0];}else{return E(_UE);}}else{return E(_Up);}}),_UP,_UQ,new T(function(){return E(E(_Vv)[1]);}),new T(function(){return E(E(_Vv)[2]);})],new T(function(){return E(E(_Vv)[3]);}),_Vu];case 48:var _UW=_UN,_V1=_UP,_UY=_UQ,_UZ=_US;_UG=_UW;_UH=_cy;_UI=_V1;_UJ=_UY;_UK=_UU;_UL=_UZ;return null;default:if((_UV-48|0)>>>0>9){var _Vx=new T(function(){var _Vy=E(_US);if(!_Vy[0]){return E(_Tr);}else{return B(A(E(_Vy[1])[1],[_UT]));}});return [0,[0,_6J,_6J,new T(function(){if(!E(_UN)){if(!E(_UO)){return [0];}else{return E(_UE);}}else{return E(_Up);}}),_UP,_UQ,new T(function(){return E(E(_Vx)[1]);}),new T(function(){return E(E(_Vx)[2]);})],new T(function(){return E(E(_Vx)[3]);}),_US];}else{var _Vz=new T(function(){var _VA=B(_7t(_Um,_UT)),_VB=_VA[2],_VC=E(_VA[1]);if(!_VC[0]){return [0,_Uq,_VB];}else{return [0,new T(function(){var _VD=B(_Ua(B(_7S(_U7,_VC))));if(!_VD[0]){return E(_Tt);}else{if(!E(_VD[2])[0]){return E(_VD[1]);}else{return E(_Tv);}}}),_VB];}}),_VE=new T(function(){var _VF=E(E(_Vz)[2]);if(!_VF[0]){return [0,_6J,_1l,_US];}else{if(E(_VF[1])==46){var _VG=E(_VF[2]);if(!_VG[0]){return [0,_UB,_UC,_US];}else{if(E(_VG[1])==42){var _VH=new T(function(){var _VI=B(_Uh(_US));return [0,_VI[1],_VI[2]];});return [0,[1,new T(function(){return E(E(_VH)[2]);})],_VG[2],new T(function(){return E(E(_VH)[1]);})];}else{var _VJ=new T(function(){var _VK=B(_7t(_Um,_VG)),_VL=_VK[2],_VM=E(_VK[1]);if(!_VM[0]){return [0,_Uq,_VL];}else{return [0,new T(function(){var _VN=B(_Ua(B(_7S(_U7,_VM))));if(!_VN[0]){return E(_Tt);}else{if(!E(_VN[2])[0]){return E(_VN[1]);}else{return E(_Tv);}}}),_VL];}});return [0,[1,new T(function(){return E(E(_VJ)[1]);})],new T(function(){return E(E(_VJ)[2]);}),_US];}}}else{return [0,_6J,_VF,_US];}}}),_VO=new T(function(){return E(E(_VE)[3]);}),_VP=new T(function(){var _VQ=E(_VO);if(!_VQ[0]){return E(_Tr);}else{return B(A(E(_VQ[1])[1],[new T(function(){return E(E(_VE)[2]);})]));}}),_VR=new T(function(){return E(E(_Vz)[1]);});return [0,[0,[1,new T(function(){return B(_Jm(_VR));})],new T(function(){return E(E(_VE)[1]);}),new T(function(){if(E(_VR)>=0){if(!E(_UN)){if(!E(_UO)){return [0];}else{return E(_UE);}}else{return E(_Up);}}else{return E(_Up);}}),_UP,_UQ,new T(function(){return E(E(_VP)[1]);}),new T(function(){return E(E(_VP)[2]);})],new T(function(){return E(E(_VP)[3]);}),_VO];}}}})(_UG,_UH,_UI,_UJ,_UK,_UL));if(_UM!=null){return _UM;}}},_VS=37,_VT=function(_VU,_VV,_VW){var _VX=E(_VU);if(!_VX[0]){return (E(_VV)[0]==0)?E(_VW):E(_BL);}else{var _VY=_VX[2],_VZ=E(_VX[1]);if(E(_VZ)==37){var _W0=function(_W1){var _W2=E(_VV);if(!_W2[0]){return E(_Tr);}else{var _W3=B(_UF(_cx,_cx,_6J,_cx,_VY,_W2)),_W4=E(_W3[3]);if(!_W4[0]){return E(_Tr);}else{return new F(function(){return A(E(_W4[1])[2],[_W3[1],new T(function(){return B(_VT(_W3[2],_W4[2],_W1));})]);});}}},_W5=E(_VY);if(!_W5[0]){return new F(function(){return _W0(_VW);});}else{if(E(_W5[1])==37){return [1,_VS,new T(function(){return B(_VT(_W5[2],_VV,_VW));})];}else{return new F(function(){return _W0(_VW);});}}}else{return [1,_VZ,new T(function(){return B(_VT(_VY,_VV,_VW));})];}}},_W6=function(_W7,_W8){return new F(function(){return _bc(_To,B(_VT(_W7,new T(function(){return B(_y5(_W8,_1l));},1),_1l)));});},_W9=function(_Wa,_Wb,_Wc,_Wd,_We){if(_Wb!=_Wd){return new F(function(){return _ww(_Wa,_Wb,_Wd);});}else{return new F(function(){return _ww(_Wa,E(_Wc),E(_We));});}},_Wf=new T(function(){return B(unCStr("%.3f"));}),_Wg=32,_Wh=new T(function(){return B(unCStr("ccdtrans sav"));}),_Wi=new T(function(){return B(unCStr("  ccdacq_nodark"));}),_Wj=new T(function(){return B(unAppCStr("}",_BE));}),_Wk=new T(function(){return B(_16(_BE,_Wj));}),_Wl=new T(function(){return B(unCStr("\""));}),_Wm=new T(function(){return B(_1g(0,1,_1l));}),_Wn=new T(function(){return B(unCStr("1"));}),_Wo=new T(function(){return B(_16(_Wn,_1l));}),_Wp=[1,_Wg,_Wo],_Wq=new T(function(){return B(_16(_Wm,_Wp));}),_Wr=[1,_Wg,_Wq],_Ws=new T(function(){var _Wt=jsShow(0);return fromJSStr(_Wt);}),_Wu=new T(function(){var _Wv=jsShow(4.0e-2);return fromJSStr(_Wv);}),_Ww=function(_Wx){return new F(function(){return _W6(_Wf,[1,[0,function(_rf){return new F(function(){return _BM(_Wx,_rf);});},function(_rf){return new F(function(){return _Tk(_Wx,_rf);});}],_1l]);});},_Wy=function(_Wz,_WA,_WB,_WC){if(!E(_Wz)){var _WD=new T(function(){var _WE=new T(function(){var _WF=E(E(_WB)[1])[2],_WG=E(_WA);if(!E(_WG[6])){return E(_WG[3])+E(_WF)*25/900;}else{return E(_WG[4])+E(_WF)*25/900;}}),_WH=new T(function(){var _WI=new T(function(){var _WJ=new T(function(){var _WK=E(_WA),_WL=_WK[5],_WM=E(_WB),_WN=E(_WM[1]),_WO=E(_WN[1]),_WP=E(_WM[2]),_WQ=E(_WP[1]),_WR=B(_W9(E(_WK[7]),_WO,_WN[2],_WQ,_WP[2])),_WS=new T(function(){var _WT=new T(function(){var _WU=new T(function(){var _WV=new T(function(){var _WW=new T(function(){var _WX=new T(function(){var _WY=new T(function(){return E(_WL)+12.5+(_WO*25/900-12.5)*Math.cos(E(_WC));}),_WZ=new T(function(){var _X0=new T(function(){var _X1=new T(function(){return (E(_WL)+12.5+(_WQ*25/900-12.5)*Math.cos(E(_WC))-E(_WY))/_WR;}),_X2=new T(function(){var _X3=new T(function(){var _X4=new T(function(){var _X5=new T(function(){return (_WO*25/900-12.5)*Math.sin(E(_WC));}),_X6=new T(function(){var _X7=new T(function(){var _X8=new T(function(){return ((_WQ*25/900-12.5)*Math.sin(E(_WC))-E(_X5))/_WR;}),_X9=new T(function(){var _Xa=new T(function(){var _Xb=new T(function(){var _Xc=new T(function(){var _Xd=new T(function(){var _Xe=new T(function(){var _Xf=new T(function(){var _Xg=new T(function(){return B(_16(B(unAppCStr("\"",new T(function(){return B(_16(_WM[3],_Wl));}))),_1l));});return B(_16(_Wu,[1,_Wg,_Xg]));});return B(_16(B(_16(_Wi,[1,_Wg,_Xf])),_Wk));},1);return B(_16(_BE,_Xe));});return B(unAppCStr("  umv tmp2 x",_Xd));},1);return B(_16(_BE,_Xc));});return B(unAppCStr("  umv sah y",_Xb));},1);return B(_16(_BE,_Xa));},1);return B(_16(B(_W6(_Wf,[1,[0,function(_rf){return new F(function(){return _BM(_X8,_rf);});},function(_rf){return new F(function(){return _Tk(_X8,_rf);});}],_1l])),_X9));});return B(unAppCStr("+i*",_X7));},1);return B(_16(B(_Ww(_X5)),_X6));});return B(unAppCStr("  x = ",_X4));},1);return B(_16(_BE,_X3));},1);return B(_16(B(_W6(_Wf,[1,[0,function(_rf){return new F(function(){return _BM(_X1,_rf);});},function(_rf){return new F(function(){return _Tk(_X1,_rf);});}],_1l])),_X2));});return B(unAppCStr("+i*",_X0));},1);return B(_16(B(_Ww(_WY)),_WZ));});return B(unAppCStr("  y = ",_WX));},1);return B(_16(_BE,_WW));});return B(unAppCStr("{",_WV));},1);return B(_16(_BE,_WU));});return B(unAppCStr(";i+=1)",_WT));},1);return B(_16(B(_1g(0,_WR,_1l)),_WS));});return B(unAppCStr("for(i=0;i<=",_WJ));},1);return B(_16(_BE,_WI));},1);return B(_16(B(_W6(_Wf,[1,[0,function(_rf){return new F(function(){return _BM(_WE,_rf);});},function(_rf){return new F(function(){return _Tk(_WE,_rf);});}],_1l])),_WH));});return new F(function(){return unAppCStr("umv sav ",_WD);});}else{var _Xh=new T(function(){var _Xi=new T(function(){return E(E(_WA)[5])+12.5+(E(E(E(_WB)[1])[1])*25/900-12.5)*Math.cos(E(_WC));}),_Xj=new T(function(){var _Xk=new T(function(){var _Xl=new T(function(){return (E(E(E(_WB)[1])[1])*25/900-12.5)*Math.sin(E(_WC));}),_Xm=new T(function(){var _Xn=new T(function(){var _Xo=new T(function(){var _Xp=new T(function(){var _Xq=E(E(_WB)[1])[2],_Xr=E(_WA);if(!E(_Xr[6])){return E(_Xr[3])+E(_Xq)*25/900;}else{return E(_Xr[4])+E(_Xq)*25/900;}}),_Xs=new T(function(){var _Xt=new T(function(){var _Xu=E(E(_WB)[2])[2],_Xv=E(_WA);if(!E(_Xv[6])){return E(_Xv[3])+E(_Xu)*25/900;}else{return E(_Xv[4])+E(_Xu)*25/900;}}),_Xw=new T(function(){var _Xx=E(_WB),_Xy=E(_Xx[1]),_Xz=E(_Xx[2]),_XA=new T(function(){var _XB=new T(function(){var _XC=new T(function(){return B(_16(B(unAppCStr("\"",new T(function(){return B(_16(_Xx[3],_Wl));}))),_Wr));});return B(_16(_Ws,[1,_Wg,_XC]));});return B(_16(_Wu,[1,_Wg,_XB]));});return B(_16(B(_1g(0,B(_W9(E(E(_WA)[7]),E(_Xy[1]),_Xy[2],E(_Xz[1]),_Xz[2])),_1l)),[1,_Wg,_XA]));});return B(_16(B(_W6(_Wf,[1,[0,function(_rf){return new F(function(){return _BM(_Xt,_rf);});},function(_rf){return new F(function(){return _Tk(_Xt,_rf);});}],_1l])),[1,_Wg,_Xw]));});return B(_16(B(_W6(_Wf,[1,[0,function(_rf){return new F(function(){return _BM(_Xp,_rf);});},function(_rf){return new F(function(){return _Tk(_Xp,_rf);});}],_1l])),[1,_Wg,_Xs]));});return B(_16(_Wh,[1,_Wg,_Xo]));},1);return B(_16(_BE,_Xn));},1);return B(_16(B(_W6(_Wf,[1,[0,function(_rf){return new F(function(){return _BM(_Xl,_rf);});},function(_rf){return new F(function(){return _Tk(_Xl,_rf);});}],_1l])),_Xm));});return B(unAppCStr(" tmp2 ",_Xk));},1);return B(_16(B(_W6(_Wf,[1,[0,function(_rf){return new F(function(){return _BM(_Xi,_rf);});},function(_rf){return new F(function(){return _Tk(_Xi,_rf);});}],_1l])),_Xj));});return new F(function(){return unAppCStr("umv sah ",_Xh);});}},_XD=function(_XE,_XF,_XG,_XH,_XI,_XJ,_XK){var _XL=[0,_BA,_XE,_XF,_XG,_XH,_XI,_XJ,_XK],_XM=function(_XN){var _XO=new T(function(){var _XP=E(_XN),_XQ=rintDouble(_XP*180/3.141592653589793),_XR=B(_x6(_XQ)),_XS=_XR[1],_XT=_XR[2],_XU=new T(function(){var _XV=new T(function(){var _XW=B(_bc(function(_XX){var _XY=E(_XX);if(E(E(_XY[1])[1])!=E(E(_XY[2])[1])){return new F(function(){return _Wy(_Bw,_XL,_XY,_XP);});}else{return new F(function(){return _Wy(_Bx,_XL,_XY,_XP);});}},B(_y5(_XE,_1l))));if(!_XW[0]){return [0];}else{return B(_BB([1,_XW[1],new T(function(){return B(_BG(_BE,_XW[2]));})]));}},1);return B(_16(_BE,_XV));});if(_XT>=0){return B(_16(B(_Bs(0,B(_ou(_XS,_XT)),_1l)),_XU));}else{var _XZ=hs_uncheckedIShiftRA64(B(_xm(_XS)), -_XT);return B(_16(B(_Bs(0,B(_xc(_XZ)),_1l)),_XU));}});return new F(function(){return unAppCStr("umv sar ",_XO);});},_Y0=B(_bc(_XM,_XK));if(!_Y0[0]){return [0];}else{return new F(function(){return _BB([1,_Y0[1],new T(function(){return B(_BG(_BF,_Y0[2]));})]);});}},_Y1=(function(id){return document.getElementById(id);}),_Y2=function(_Y3,_Y4){var _Y5=function(_){var _Y6=E(_Y1)(E(_Y4)),_Y7=__eq(_Y6,E(_uv));return (E(_Y7)==0)?[1,_Y6]:_6J;};return new F(function(){return A(_2,[_Y3,_Y5]);});},_Y8=new T(function(){return B(unCStr("\n"));}),_Y9=function(_Ya,_Yb,_){var _Yc=jsWriteHandle(E(_Ya),toJSStr(E(_Yb)));return _a;},_Yd=function(_Ye,_Yf,_){var _Yg=E(_Ye),_Yh=jsWriteHandle(_Yg,toJSStr(E(_Yf)));return new F(function(){return _Y9(_Yg,_Y8,_);});},_Yi=34,_Yj=[1,_Yi,_1l],_Yk=new T(function(){return B(unCStr("\\\""));}),_Yl=function(_Ym,_Yn){var _Yo=E(_Ym);if(!_Yo[0]){return E(_Yn);}else{var _Yp=_Yo[2],_Yq=E(_Yo[1]);if(_Yq==34){return new F(function(){return _16(_Yk,new T(function(){return B(_Yl(_Yp,_Yn));},1));});}else{return new F(function(){return _Dk(_Yq,new T(function(){return B(_Yl(_Yp,_Yn));}));});}}},_Yr=function(_){return new F(function(){return jsMkStdout();});},_Ys=new T(function(){return B(_ur(_Yr));}),_Yt=function(_Yu,_Yv,_Yw,_){var _Yx=B(A(_Y2,[_6R,new T(function(){return toJSStr(E(_Yu));},1),_])),_Yy=E(_Yx);if(!_Yy[0]){var _Yz=new T(function(){var _YA=new T(function(){return B(_16(_Yv,new T(function(){return B(unAppCStr("on page element ",_Yu));},1)));});return B(_Yl(B(unAppCStr("Failed to set ",_YA)),_Yj));}),_YB=B(_Yd(_Ys,[1,_Yi,_Yz],_));return _a;}else{var _YC=E(_v5)(E(_Yy[1]),toJSStr(E(_Yv)),toJSStr(E(_Yw)));return _a;}},_YD=new T(function(){return encodeURIComponent;}),_YE=new T(function(){return B(unCStr("data:text/plain;charset=utf-8,"));}),_YF=new T(function(){return B(unCStr("href"));}),_YG=function(_YH,_YI,_){var _YJ=E(_YD)(toJSStr(_YI)),_YK=new T(function(){return B(_16(_YE,new T(function(){var _YL=String(_YJ);return fromJSStr(_YL);},1)));},1);return new F(function(){return _Yt(_YH,_YF,_YK,_);});},_YM="scans",_YN=new T(function(){return B(_Y2(_6R,_YM));}),_YO=(function(ctx,rad){ctx.rotate(rad);}),_YP=function(_YQ,_YR,_YS,_){var _YT=E(_Af)(_YS),_YU=E(_YO)(_YS,E(_YQ)),_YV=B(A(_YR,[_YS,_])),_YW=E(_Ae)(_YS);return new F(function(){return _Ad(_);});},_YX=(function(ctx,x,y){ctx.translate(x,y);}),_YY=function(_YZ,_Z0,_Z1,_Z2,_){var _Z3=E(_Af)(_Z2),_Z4=E(_YX)(_Z2,E(_YZ),E(_Z0)),_Z5=B(A(_Z1,[_Z2,_])),_Z6=E(_Ae)(_Z2);return new F(function(){return _Ad(_);});},_Z7=function(_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf){return new F(function(){return Math.atan((Math.tan(B(_ER(new T(function(){return B(_E9(_Zb,_Z9));}),_Za-_Z8))-1.5707963267948966)+Math.tan(B(_ER(new T(function(){return B(_E9(_Zd,_Zb));}),_Zc-_Za)))+Math.tan(B(_ER(new T(function(){return B(_E9(_Zf,_Zd));}),_Ze-_Zc))+1.5707963267948966)+Math.tan(B(_ER(new T(function(){return B(_E9(_Z9,_Zf));}),_Z8-_Ze))-3.141592653589793))/4);});},_Zg=function(_Zh){return E(_Zh)/2;},_Zi=function(_Zj,_Zk,_Zl,_){var _Zm=E(_Zj);return new F(function(){return _YY(_Zm[1],_Zm[2],_Zk,E(_Zl),_);});},_Zn=function(_Zo,_Zp){var _Zq=new T(function(){var _Zr=E(_Zo),_Zs=E(E(_Zp)[2]),_Zt=E(_Zs[1]),_Zu=E(_Zt[1]),_Zv=E(_Zt[2]),_Zw=E(_Zs[2]),_Zx=E(_Zw[1]),_Zy=E(_Zw[2]),_Zz=E(_Zs[3]),_ZA=E(_Zz[1]),_ZB=E(_Zz[2]),_ZC=E(_Zs[4]),_ZD=E(_ZC[1]),_ZE=E(_ZC[2]);return Math.sqrt(E(_Zr[1])*E(_Zr[2])/(0.5*(_Zu*_ZE+_ZD*_ZB+_ZA*_Zv-_Zu*_ZB-_ZA*_ZE-_ZD*_Zv)+0.5*(_ZD*_ZB+_ZA*_Zy+_Zx*_ZE-_ZD*_Zy-_Zx*_ZB-_ZA*_ZE)));}),_ZF=new T(function(){var _ZG=E(_Zo);return [0,new T(function(){return B(_Zg(_ZG[1]));}),new T(function(){return B(_Zg(_ZG[2]));})];}),_ZH=new T(function(){var _ZI=E(E(_Zp)[2]),_ZJ=E(_ZI[1]),_ZK=E(_ZI[2]),_ZL=E(_ZI[3]),_ZM=E(_ZI[4]);return  -B(_Z7(E(_ZJ[1]),_ZJ[2],E(_ZK[1]),_ZK[2],E(_ZL[1]),_ZL[2],E(_ZM[1]),_ZM[2]));}),_ZN=new T(function(){var _ZO=E(E(_Zp)[2]),_ZP=E(_ZO[1]),_ZQ=E(_ZO[2]),_ZR=E(_ZO[3]),_ZS=E(_ZO[4]);return [0,new T(function(){return (E(_ZP[1])+E(_ZQ[1])+E(_ZR[1])+E(_ZS[1]))/4/(-1);}),new T(function(){return (E(_ZP[2])+E(_ZQ[2])+E(_ZR[2])+E(_ZS[2]))/4/(-1);})];}),_ZT=function(_ZU,_ZV,_){var _ZW=E(_ZF),_ZX=function(_ZY,_){var _ZZ=function(_100,_){return new F(function(){return _YP(_ZH,function(_101,_){return new F(function(){return _Zi(_ZN,_ZU,_101,_);});},E(_100),_);});};return new F(function(){return _Ah(_Zq,_Zq,_ZZ,E(_ZY),_);});};return new F(function(){return _YY(_ZW[1],_ZW[2],_ZX,E(_ZV),_);});};return E(_ZT);},_102=(function(ctx,x,y){ctx.moveTo(x,y);}),_103=(function(ctx,x,y){ctx.lineTo(x,y);}),_104=function(_105,_106,_){var _107=E(_105);if(!_107[0]){return _a;}else{var _108=E(_107[1]),_109=E(_106),_10a=E(_102)(_109,E(_108[1]),E(_108[2])),_10b=E(_107[2]);if(!_10b[0]){return _a;}else{var _10c=E(_10b[1]),_10d=E(_103),_10e=_10d(_109,E(_10c[1]),E(_10c[2])),_10f=_10b[2];while(1){var _10g=E(_10f);if(!_10g[0]){return _a;}else{var _10h=E(_10g[1]),_10i=_10d(_109,E(_10h[1]),E(_10h[2]));_10f=_10g[2];continue;}}}}},_10j=function(_10k,_10l,_){var _10m=new T(function(){return E(E(_10k)[2]);}),_10n=new T(function(){return E(E(_10m)[1]);});return new F(function(){return _104([1,_10n,[1,new T(function(){return E(E(_10m)[2]);}),[1,new T(function(){return E(E(_10m)[3]);}),[1,new T(function(){return E(E(_10m)[4]);}),[1,_10n,_1l]]]]],_10l,_);});},_10o=(function(e){e.width = e.width;}),_10p=",",_10q="rgba(",_10r=new T(function(){return toJSStr(_1l);}),_10s="rgb(",_10t=")",_10u=[1,_10t,_1l],_10v=function(_10w){var _10x=E(_10w);if(!_10x[0]){var _10y=jsCat([1,_10s,[1,new T(function(){return String(_10x[1]);}),[1,_10p,[1,new T(function(){return String(_10x[2]);}),[1,_10p,[1,new T(function(){return String(_10x[3]);}),_10u]]]]]],E(_10r));return E(_10y);}else{var _10z=jsCat([1,_10q,[1,new T(function(){return String(_10x[1]);}),[1,_10p,[1,new T(function(){return String(_10x[2]);}),[1,_10p,[1,new T(function(){return String(_10x[3]);}),[1,_10p,[1,new T(function(){return String(_10x[4]);}),_10u]]]]]]]],E(_10r));return E(_10z);}},_10A="strokeStyle",_10B="fillStyle",_10C=(function(e,p){return e[p].toString();}),_10D=function(_10E,_10F){var _10G=new T(function(){return B(_10v(_10E));});return function(_10H,_){var _10I=E(_10H),_10J=E(_10B),_10K=E(_10C),_10L=_10K(_10I,_10J),_10M=E(_10A),_10N=_10K(_10I,_10M),_10O=E(_10G),_10P=E(_1),_10Q=_10P(_10I,_10J,_10O),_10R=_10P(_10I,_10M,_10O),_10S=B(A(_10F,[_10I,_])),_10T=String(_10L),_10U=_10P(_10I,_10J,_10T),_10V=String(_10N),_10W=_10P(_10I,_10M,_10V);return new F(function(){return _Ad(_);});};},_10X=function(_10Y,_10Z,_110){var _111=E(_110);if(!_111[0]){return [0];}else{var _112=_111[1],_113=_111[2];return (!B(A(_10Y,[_10Z,_112])))?[1,_112,new T(function(){return B(_10X(_10Y,_10Z,_113));})]:E(_113);}},_114="lineWidth",_115=function(_116,_117){var _118=new T(function(){return String(E(_116));});return function(_119,_){var _11a=E(_119),_11b=E(_114),_11c=E(_10C)(_11a,_11b),_11d=E(_1),_11e=_11d(_11a,_11b,E(_118)),_11f=B(A(_117,[_11a,_])),_11g=String(_11c),_11h=_11d(_11a,_11b,_11g);return new F(function(){return _Ad(_);});};},_11i=1,_11j=0.2,_11k=900,_11l=[0,_11k,_11k],_11m=new T(function(){return B(unCStr("saveLink"));}),_11n=new T(function(){return B(unCStr("exportLink"));}),_11o=new T(function(){return B(unCStr(" disabled"));}),_11p=new T(function(){return B(unCStr("class"));}),_11q="aligned",_11r=new T(function(){return B(unCStr("page missing element for update"));}),_11s=[1,_Yi,_1l],_11t=new T(function(){return B(_Yl(_11r,_11s));}),_11u=[1,_Yi,_11t],_11v="original",_11w=[0,255,0,255],_11x=function(_11y,_11z,_){while(1){var _11A=E(_11y);if(!_11A[0]){return _a;}else{var _11B=E(_11A[1]),_11C=B(_104([1,_11B[1],[1,_11B[2],_1l]],_11z,_));_11y=_11A[2];continue;}}},_11D=[0,255,0,255],_11E=1,_11F=function(_11G){var _11H=new T(function(){var _11I=function(_qJ,_11J){return new F(function(){return _11x(E(_11G)[2],_qJ,_11J);});};return B(_10D(_11D,function(_11K,_){return new F(function(){return _As(_11I,E(_11K),_);});}));});return new F(function(){return _115(_11E,_11H);});},_11L=function(_11M){while(1){var _11N=E(_11M);if(!_11N[0]){return false;}else{var _11O=E(_11N[1]);if(!_11O[0]){return true;}else{if(!B(_cp(_8D,_Wg,_11O))){_11M=_11N[2];continue;}else{return true;}}}}},_11P=function(_11Q){return E(E(_11Q)[3]);},_11R=function(_11S){return new F(function(){return fromJSStr(E(_11S));});},_11T=function(_11U,_11V,_11W,_11X){var _11Y=new T(function(){var _11Z=function(_){var _120=E(_10C)(B(A(_v3,[_11U,_11W])),E(_11X));return new T(function(){return String(_120);});};return E(_11Z);});return new F(function(){return A(_2,[_11V,_11Y]);});},_121=function(_122,_123,_124,_125){var _126=B(_uY(_123)),_127=new T(function(){return B(_rR(_126));}),_128=function(_129){return new F(function(){return A(_127,[new T(function(){return B(_11R(_129));})]);});},_12a=new T(function(){return B(_11T(_122,_123,_124,new T(function(){return toJSStr(E(_125));},1)));});return new F(function(){return A(_rP,[_126,_12a,_128]);});},_12b=new T(function(){return B(unCStr("value"));}),_12c=function(_12d,_12e,_12f){var _12g=E(_12f);if(!_12g[0]){return [0];}else{var _12h=_12g[1],_12i=_12g[2];return (!B(A(_12d,[_12h])))?[1,_12h,new T(function(){return B(_12c(_12d,_12e,_12i));})]:[1,new T(function(){return B(A(_12e,[_12h]));}),new T(function(){return B(_12c(_12d,_12e,_12i));})];}},_12j=function(_12k,_12l,_12m,_12n,_){var _12o=B(A(_121,[_S,_6R,_12m,_12b,_])),_12p=_12o,_12q=E(_12l),_12r=rMV(_12q),_12s=E(_12r),_12t=new T(function(){return B(_12c(function(_12u){return new F(function(){return _sF(_12u,_12n);});},function(_12v){var _12w=E(_12v);return [0,_12w[1],_12w[2],_12p];},_12s[2]));}),_=wMV(_12q,[0,_12s[1],_12t,_12s[3],_12s[4],_12s[5],_12s[6],_12s[7],_12s[8]]);return new F(function(){return A(_12k,[_]);});},_12x=function(_12y,_12z,_12A,_){var _12B=rMV(_12z),_12C=_12B,_12D=E(_12y),_12E=rMV(_12D),_12F=new T(function(){return B(unAppCStr("btn btn-primary",new T(function(){var _12G=E(_12E),_12H=E(_12G[2]);if(!_12H[0]){return E(_11o);}else{if(!B(_11L(B(_bc(_11P,_12H))))){if(!E(_12G[8])[0]){return E(_11o);}else{return [0];}}else{return E(_11o);}}})));},1),_12I=B(_Yt(_11n,_11p,_12F,_)),_12J=E(_12E),_12K=B(_YG(_11n,B(_XD(_12J[2],_12J[3],_12J[4],_12J[5],_12J[6],_12J[7],_12J[8])),_)),_12L=B(_YG(_11m,fromJSStr(B(_Bh([4,E(B(_tt(_sP,[1,new T(function(){return [4,E(B(_t7(_12C)))];}),[1,new T(function(){return [4,E(B(_ty(_12J)))];}),_1l]])))]))),_)),_12M=B(A(_Y2,[_6R,_11v,_])),_12N=E(_12M);if(!_12N[0]){var _12O=B(_Yd(_Ys,_11u,_));return _a;}else{var _12P=E(_12N[1]),_12Q=E(_N),_12R=_12Q(_12P);if(!_12R){var _12S=B(_Yd(_Ys,_11u,_));return _a;}else{var _12T=E(_M),_12U=_12T(_12P),_12V=_12U,_12W=B(A(_Y2,[_6R,_11q,_])),_12X=function(_,_12Y){var _12Z=E(_12Y);if(!_12Z[0]){var _130=B(_Yd(_Ys,_11u,_));return _a;}else{var _131=B(A(_YN,[_])),_132=E(_131);if(!_132[0]){var _133=B(_Yd(_Ys,_11u,_));return _a;}else{var _134=function(_135,_){var _136=rMV(_12D),_137=E(_136),_=wMV(_12D,[0,_137[1],new T(function(){return B(_10X(_sF,_135,_137[2]));}),_137[3],_137[4],_137[5],_137[6],_137[7],_137[8]]);return new F(function(){return _12x(_12D,_12z,_12A,_);});},_138=function(_){return new F(function(){return _12x(_12D,_12z,_12A,_);});},_139=B(_ya(function(_si,_sa,_){return new F(function(){return _12j(_138,_12D,_si,_sa,_);});},_134,_12J,E(_132[1]),_)),_13a=E(_12A),_13b=rMV(_13a),_13c=_13b,_13d=E(_12Z[1]),_13e=_13d[1],_13f=E(_10o),_13g=_13f(_13d[2]),_13h=function(_13i,_){return new F(function(){return _Az(E(_13c),0,0,E(_13i),_);});},_13j=B(A(_Zn,[_11l,_12C,function(_13k,_){return new F(function(){return _Ah(_11j,_11j,_13h,E(_13k),_);});},_13e,_])),_13l=B(A(_11F,[_12J,_13e,_])),_13m=rMV(_13a),_13n=_13m,_13o=_13f(_12P),_13p=B(_Ah(_11j,_11j,function(_13q,_){return new F(function(){return _Az(E(_13n),0,0,E(_13q),_);});},_12V,_)),_13r=new T(function(){var _13s=function(_sa,_){return new F(function(){return _10j(_12C,_sa,_);});};return B(_10D(_11w,function(_13t,_){return new F(function(){return _As(_13s,E(_13t),_);});}));}),_13u=B(A(_115,[_11i,_13r,_12V,_]));return _a;}}},_13v=E(_12W);if(!_13v[0]){return new F(function(){return _12X(_,_6J);});}else{var _13w=E(_13v[1]),_13x=_12Q(_13w);if(!_13x){return new F(function(){return _12X(_,_6J);});}else{var _13y=_12T(_13w);return new F(function(){return _12X(_,[1,[0,_13y,_13w]]);});}}}}},_13z=2,_13A="offset",_13B=new T(function(){return B(_Y2(_6R,_13A));}),_13C="bottom",_13D=new T(function(){return B(_Y2(_6R,_13C));}),_13E=new T(function(){return B(unCStr("loadPath"));}),_13F=function(_){var _13G=function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);},_13H=E(_13G)("processDump",toJSStr(_13E));return new F(function(){return _Ad(_);});},_13I=function(_13J,_){return new F(function(){return _13F(_);});},_13K="top",_13L=new T(function(){return B(_Y2(_6R,_13K));}),_13M=new T(function(){return B(unCStr("value"));}),_13N=function(_13O,_){var _13P=B(A(_Y2,[_6R,new T(function(){return toJSStr(E(_13O));},1),_])),_13Q=E(_13P);if(!_13Q[0]){return _6J;}else{return new F(function(){return A(_121,[_S,_st,_13Q[1],_13M,_]);});}},_13R="stepSize",_13S=new T(function(){return B(_Y2(_6R,_13R));}),_13T="loadPath",_13U=new T(function(){return B(_Y2(_6R,_13T));}),_13V=function(_13W){return E(_13W)[2];},_13X=function(_){return _6J;},_13Y=function(_13Z,_){return new F(function(){return _13X(_);});},_140=[0,_13V,_13Y],_141=function(_142,_143){while(1){var _144=E(_142);if(!_144[0]){return E(_143);}else{var _145=_144[2],_146=E(_144[1]);if(_143>_146){_142=_145;_143=_146;continue;}else{_142=_145;continue;}}}},_147=function(_148,_149,_14a){var _14b=E(_148);if(_14a>_14b){return new F(function(){return _141(_149,_14b);});}else{return new F(function(){return _141(_149,_14a);});}},_14c=2,_14d=4,_14e=3,_14f=function(_14g,_14h){var _14i=function(_14j,_14k){while(1){var _14l=B((function(_14m,_14n){var _14o=E(_14m);if(!_14o[0]){return [0];}else{var _14p=_14o[2];if(!B(A(_14g,[_14o[1]]))){var _14q=_14n+1|0;_14j=_14p;_14k=_14q;return null;}else{return [1,_14n,new T(function(){return B(_14i(_14p,_14n+1|0));})];}}})(_14j,_14k));if(_14l!=null){return _14l;}}},_14r=B(_14i(_14h,0));return (_14r[0]==0)?[0]:[1,_14r[1]];},_14s=function(_14t){return E(_14t);},_14u=function(_14v,_14w,_14x,_){var _14y=function(_14z,_){var _14A=E(_14v),_14B=rMV(_14A),_14C=E(E(_14B)[2]),_14D=new T(function(){var _14E=new T(function(){var _14F=E(E(_14z)[1]);return [0,new T(function(){return B(_14s(_14F[1]));}),new T(function(){return B(_14s(_14F[2]));})];}),_14G=new T(function(){var _14H=E(_14E),_14I=E(_14C[1]);return Math.pow(E(_14H[1])-E(_14I[1]),2)+Math.pow(E(_14H[2])-E(_14I[2]),2);}),_14J=new T(function(){var _14K=E(_14E),_14L=E(_14C[2]);return Math.pow(E(_14K[1])-E(_14L[1]),2)+Math.pow(E(_14K[2])-E(_14L[2]),2);}),_14M=[1,new T(function(){var _14N=E(_14E),_14O=E(_14C[3]);return Math.pow(E(_14N[1])-E(_14O[1]),2)+Math.pow(E(_14N[2])-E(_14O[2]),2);}),[1,new T(function(){var _14P=E(_14E),_14Q=E(_14C[4]);return Math.pow(E(_14P[1])-E(_14Q[1]),2)+Math.pow(E(_14P[2])-E(_14Q[2]),2);}),_1l]],_14R=new T(function(){return B(_147(_14J,_14M,E(_14G)));}),_14S=B(_14f(function(_14T){return E(_14R)==E(_14T);},[1,_14G,[1,_14J,_14M]]));if(!_14S[0]){return 3;}else{switch(E(_14S[1])){case 0:return 0;break;case 1:return 2;break;case 3:return 1;break;default:return 3;}}}),_=wMV(_14A,[0,[1,_14D],_14C]);return new F(function(){return A(_14x,[_]);});},_14U=B(A(_xD,[_6S,_140,_uW,_14w,_14c,_14y,_])),_14V=B(A(_xD,[_6S,_140,_uW,_14w,_14e,function(_14W,_){var _14X=E(_14v),_14Y=rMV(_14X),_=wMV(_14X,[0,_1V,E(_14Y)[2]]);return new F(function(){return A(_14x,[_]);});},_])),_14Z=function(_150,_){var _151=E(_14v),_152=rMV(_151),_153=E(_152),_154=_153[2],_155=E(_153[1]);if(!_155[0]){var _156=E(_153);}else{var _157=new T(function(){var _158=E(E(_150)[1]);return [0,new T(function(){return B(_14s(_158[1]));}),new T(function(){return B(_14s(_158[2]));})];});switch(E(_155[1])){case 0:var _159=E(_154),_15a=[0,_155,[0,_157,_159[2],_159[3],_159[4]]];break;case 1:var _15b=E(_154),_15a=[0,_155,[0,_15b[1],_15b[2],_15b[3],_157]];break;case 2:var _15c=E(_154),_15a=[0,_155,[0,_15c[1],_157,_15c[3],_15c[4]]];break;default:var _15d=E(_154),_15a=[0,_155,[0,_15d[1],_15d[2],_157,_15d[4]]];}var _156=_15a;}var _=wMV(_151,_156);return new F(function(){return A(_14x,[_]);});},_15e=B(A(_xD,[_6S,_140,_uW,_14w,_14d,_14Z,_]));return _a;},_15f=function(_15g,_15h,_15i,_15j,_15k,_15l,_15m,_15n,_15o){if(!E(_15h)){return [0,_31,_15i,_15j,_15k,_15l,_15m,_15n,_15o];}else{var _15p=E(_15i);if(!_15p[0]){return [0,_2Z,_1l,_15j,_15k,_15l,_15m,_15n,_15o];}else{var _15q=new T(function(){return E(E(_15p[1])[1]);});return [0,_2Z,[1,[0,_15q,new T(function(){var _15r=E(_15q),_15s=_15r[1],_15t=E(E(_15g)[1]),_15u=_15t[1],_15v=E(_15t[2]),_15w=E(_15r[2]),_15x=_15v-_15w;if(!_15x){var _15y=E(_15u),_15z=E(_15s),_15A=_15y-_15z;if(!_15A){return [0,_15y,_15w];}else{if(_15A<=0){if(0<= -_15A){return [0,_15y,_15w];}else{return [0,_15z,_15v];}}else{if(0<=_15A){return [0,_15y,_15w];}else{return [0,_15z,_15v];}}}}else{if(_15x<=0){var _15B=E(_15u),_15C=E(_15s),_15D=_15B-_15C;if(!_15D){if( -_15x<=0){return [0,_15B,_15w];}else{return [0,_15C,_15v];}}else{if(_15D<=0){if( -_15x<= -_15D){return [0,_15B,_15w];}else{return [0,_15C,_15v];}}else{if( -_15x<=_15D){return [0,_15B,_15w];}else{return [0,_15C,_15v];}}}}else{var _15E=E(_15u),_15F=E(_15s),_15G=_15E-_15F;if(!_15G){return [0,_15F,_15v];}else{if(_15G<=0){if(_15x<= -_15G){return [0,_15E,_15w];}else{return [0,_15F,_15v];}}else{if(_15x<=_15G){return [0,_15E,_15w];}else{return [0,_15F,_15v];}}}}}}),_1l],_15p[2]],_15j,_15k,_15l,_15m,_15n,_15o];}}},_15H=function(_15I,_15J,_15K,_){var _15L=function(_15M,_){var _15N=E(_15I),_15O=rMV(_15N),_15P=E(_15O),_15Q=new T(function(){var _15R=E(E(_15M)[1]);return [0,new T(function(){return B(_14s(_15R[1]));}),new T(function(){return B(_14s(_15R[2]));})];}),_=wMV(_15N,[0,_2Z,[1,[0,_15Q,_15Q,_1l],_15P[2]],_15P[3],_15P[4],_15P[5],_15P[6],_15P[7],_15P[8]]);return new F(function(){return A(_15K,[_]);});},_15S=B(A(_xD,[_6S,_140,_uW,_15J,_14c,_15L,_])),_15T=B(A(_xD,[_6S,_140,_uW,_15J,_14e,function(_15U,_){var _15V=E(_15I),_15W=rMV(_15V),_15X=E(_15W),_15Y=B(_15f(_15U,_15X[1],_15X[2],_15X[3],_15X[4],_15X[5],_15X[6],_15X[7],_15X[8])),_=wMV(_15V,[0,_31,_15Y[2],_15Y[3],_15Y[4],_15Y[5],_15Y[6],_15Y[7],_15Y[8]]);return new F(function(){return A(_15K,[_]);});},_])),_15Z=B(A(_xD,[_6S,_140,_uW,_15J,_14d,function(_160,_){var _161=E(_15I),_162=rMV(_161),_163=E(_162),_164=B(_15f(_160,_163[1],_163[2],_163[3],_163[4],_163[5],_163[6],_163[7],_163[8])),_=wMV(_161,[0,_164[1],_164[2],_164[3],_164[4],_164[5],_164[6],_164[7],_164[8]]);return new F(function(){return A(_15K,[_]);});},_]));return _a;},_165=new T(function(){return document;}),_166=function(_167,_){var _168=E(_167);if(!_168[0]){return _1l;}else{var _169=B(_166(_168[2],_));return [1,_168[1],_169];}},_16a=function(_16b,_){var _16c=__arr2lst(0,_16b);return new F(function(){return _166(_16c,_);});},_16d=(function(e,q){if(!e || typeof e.querySelectorAll !== 'function') {return [];} else {return e.querySelectorAll(q);}}),_16e=function(_16f,_16g,_16h){var _16i=function(_){var _16j=E(_16d)(E(_16g),toJSStr(E(_16h)));return new F(function(){return _16a(_16j,_);});};return new F(function(){return A(_2,[_16f,_16i]);});},_16k=(function(x){return document.getElementById(x).value;}),_16l=(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);}),_16m=0,_16n=[0,_16m,_16m],_16o=653,_16p=[0,_16o,_16m],_16q=986,_16r=[0,_16o,_16q],_16s=[0,_16m,_16q],_16t=[0,_16n,_16s,_16r,_16p],_16u=[0,_1V,_16t],_16v=50,_16w=5,_16x=0,_16y=function(_16z,_16A,_16B){var _16C=E(_16A),_16D=E(_16B),_16E=new T(function(){var _16F=B(_Mr(_16z)),_16G=B(_16y(_16z,_16D,B(A(_Kt,[_16F,new T(function(){return B(A(_Lo,[_16F,_16D,_16D]));}),_16C]))));return [1,_16G[1],_16G[2]];});return [0,_16C,_16E];},_16H=function(_16I){return E(E(_16I)[2]);},_16J=function(_16K){return E(E(_16K)[4]);},_16L=function(_16M){return E(E(_16M)[6]);},_16N=function(_16O,_16P){var _16Q=E(_16P);if(!_16Q[0]){return [0];}else{var _16R=_16Q[1];return (!B(A(_16O,[_16R])))?[0]:[1,_16R,new T(function(){return B(_16N(_16O,_16Q[2]));})];}},_16S=function(_16T,_16U,_16V,_16W,_16X){var _16Y=B(_16y(_16U,_16V,_16W)),_16Z=new T(function(){var _170=new T(function(){return B(_Mr(_16U));}),_171=new T(function(){return B(A(_16H,[_16U,new T(function(){return B(A(_Kt,[_170,_16W,_16V]));}),new T(function(){return B(A(_Kx,[_170,_mg]));})]));});if(!B(A(_16L,[_16T,_16W,_16V]))){var _172=new T(function(){return B(A(_Lo,[_170,_16X,_171]));});return function(_173){return new F(function(){return A(_16L,[_16T,_173,_172]);});};}else{var _174=new T(function(){return B(A(_Lo,[_170,_16X,_171]));});return function(_175){return new F(function(){return A(_16J,[_16T,_175,_174]);});};}});return new F(function(){return _16N(_16Z,[1,_16Y[1],_16Y[2]]);});},_176=new T(function(){return B(_16S(_GB,_Eo,_16x,_16w,_16v));}),_177=function(_178){return E(_178)*1.7453292519943295e-2;},_179=new T(function(){return B(_bc(_177,_176));}),_17a=0.5,_17b=[0,_31,_1l,_16x,_16v,_16x,_2R,_17a,_179],_17c=[1,_a],_17d=new T(function(){return B(unCStr("Page Missing element expected by Main"));}),_17e=new T(function(){return B(_Yl(_17d,_Yj));}),_17f=[1,_Yi,_17e],_17g=new T(function(){return B(unCStr("Could not read offset elements"));}),_17h=new T(function(){return B(_Yl(_17g,_Yj));}),_17i=[1,_Yi,_17h],_17j=new T(function(){return B(unCStr("input[name=\'mount\']:checked"));}),_17k=new T(function(){return B(unCStr("offset"));}),_17l=new T(function(){return B(unCStr("bottom"));}),_17m=new T(function(){return B(unCStr("top"));}),_17n=new T(function(){return B(unCStr("Could not load element step size"));}),_17o=new T(function(){return B(_Yl(_17n,_Yj));}),_17p=[1,_Yi,_17o],_17q=new T(function(){return B(unCStr("stepSize"));}),_17r=new T(function(){return B(unCStr("Could not read rotations"));}),_17s=new T(function(){return B(_Yl(_17r,_Yj));}),_17t=[1,_Yi,_17s],_17u=34,_17v=new T(function(){return B(unCStr("do not use readS_to_P in gather!"));}),_17w=new T(function(){return B(err(_17v));}),_17x=function(_17y,_17z){var _17A=E(_17z);switch(_17A[0]){case 0:return [0,function(_17B){return new F(function(){return _17x(function(_17C){return new F(function(){return A(_17y,[[1,_17B,_17C]]);});},B(A(_17A[1],[_17B])));});}];case 1:return [1,function(_17D){return new F(function(){return _17x(_17y,B(A(_17A[1],[_17D])));});}];case 2:return [2];case 3:return new F(function(){return _82(B(A(_17A[1],[new T(function(){return B(A(_17y,[_1l]));})])),new T(function(){return B(_17x(_17y,_17A[2]));}));});break;default:return E(_17w);}},_17E=[3,_8Z,_8Y],_17F=function(_17G){return E(_17E);},_17H=new T(function(){return B(_jm(_17F));}),_17I=new T(function(){return B(_17x(_Q,_17H));}),_17J=function(_17K){return E(_17I);},_17L=function(_17M){return new F(function(){return A(_i3,[_17M,_17J]);});},_17N=[1,_17L],_17O=function(_17P){var _17Q=E(_17P);if(!_17Q[0]){return [0];}else{var _17R=E(_17Q[1]),_17S=new T(function(){return B(_17O(_17Q[2]));}),_17T=function(_17U){while(1){var _17V=B((function(_17W){var _17X=E(_17W);if(!_17X[0]){return E(_17S);}else{var _17Y=_17X[2],_17Z=E(_17X[1]);if(!E(_17Z[1])[0]){if(!E(_17Z[2])[0]){return [1,_17R[1],new T(function(){return B(_17T(_17Y));})];}else{_17U=_17Y;return null;}}else{_17U=_17Y;return null;}}})(_17U));if(_17V!=null){return _17V;}}};return new F(function(){return _17T(B(_7S(_17N,_17R[2])));});}},_180=new T(function(){return B(unCStr("\""));}),_181=new T(function(){return B(unCStr("...\""));}),_182=12,_183=function(_184){return E(E(_184)[1]);},_185=function(_186,_187){var _188=new T(function(){var _189=B(_Qj(_182,_187));return B(_16(_189[1],new T(function(){if(B(_b7(_187,0))>15){return E(_181);}else{return B(_16(_189[2],_180));}},1)));}),_18a=B(_17O(B(A(_183,[_186,_jT,_187]))));return (_18a[0]==0)?[0,new T(function(){return B(unAppCStr("no parse on ",[1,_17u,_188]));})]:(E(_18a[2])[0]==0)?[1,_18a[1]]:[0,new T(function(){return B(unAppCStr("ambiguous parse on ",[1,_17u,_188]));})];},_18b=function(_18c,_18d){var _18e=B(_185(_qM,_18c));if(!_18e[0]){return [0];}else{var _18f=E(_18d);return (_18f[0]==0)?[0]:[1,[1,_18e[1],_18f[1]]];}},_18g=[1,_1l],_18h=new T(function(){return B(unCStr("rotations"));}),_18i="rotations",_18j=new T(function(){return B(unCStr("download"));}),_18k=new T(function(){return B(unCStr(".txt"));}),_18l=new T(function(){return B(unCStr(".json"));}),_18m=new T(function(){return B(unCStr("filePath"));}),_18n="filePath",_18o=new T(function(){return B(unCStr("failed to decode JSON"));}),_18p=[1,_Yi,_1l],_18q=new T(function(){return B(_Yl(_18o,_18p));}),_18r=[1,_Yi,_18q],_18s=new T(function(){return B(unCStr("input[name=\'mount\']"));}),_18t=new T(function(){return B(unCStr("IndianRoller2.jpg"));}),_18u=function(_18v){return E(_18v)*1.7453292519943295e-2;},_18w=function(_18x,_18y){var _18z=E(_18y);if(!_18z[0]){return [0,_1l,_1l];}else{var _18A=_18z[1];if(!B(A(_18x,[_18A]))){var _18B=new T(function(){var _18C=B(_18w(_18x,_18z[2]));return [0,_18C[1],_18C[2]];});return [0,[1,_18A,new T(function(){return E(E(_18B)[1]);})],new T(function(){return E(E(_18B)[2]);})];}else{return [0,_1l,_18z];}}},_18D=function(_18E){var _18F=_18E>>>0;if(_18F>887){var _18G=u_iswspace(_18E);return (E(_18G)==0)?false:true;}else{var _18H=E(_18F);return (_18H==32)?true:(_18H-9>>>0>4)?(E(_18H)==160)?true:false:true;}},_18I=function(_18J){return new F(function(){return _18D(E(_18J));});},_18K=function(_18L,_18M,_18N){var _18O=function(_18P){var _18Q=B(_no(_18I,_18P));if(!_18Q[0]){return E(_18M);}else{var _18R=new T(function(){var _18S=B(_18w(_18I,_18Q));return [0,_18S[1],_18S[2]];});return new F(function(){return A(_18L,[new T(function(){return E(E(_18R)[1]);}),new T(function(){return B(_18O(E(_18R)[2]));})]);});}};return new F(function(){return _18O(_18N);});},_18T=function(_){var _18U=nMV(_16u),_18V=_18U,_18W=nMV(_17b),_18X=_18W,_18Y=B(A(_5,[_6R,_18t,_])),_18Z=nMV(_18Y),_190=_18Z,_191=nMV(_18t),_192=_191,_193=B(A(_16e,[_6R,_165,_18s,_])),_194=_193,_195=function(_196,_){var _197=String(E(_196)),_198=jsParseJSON(_197);if(!_198[0]){var _199=B(_Yd(_Ys,_18r,_));return _uv;}else{var _19a=B(_4u(_198[1]));if(!_19a[0]){var _19b=B(_Yd(_Ys,_18r,_));return _uv;}else{var _19c=_19a[1],_=wMV(_18V,new T(function(){return E(E(_19c)[1]);})),_=wMV(_18X,new T(function(){return E(E(_19c)[2]);}));return _uv;}}},_19d=__createJSFunc(2,E(_195)),_19e=(function(s,f){Haste[s] = f;}),_19f=E(_19e)("processDump",_19d),_19g=B(A(_Y2,[_6R,_18n,_])),_19h=E(_19g);if(!_19h[0]){var _19i=B(_Yd(_Ys,_17f,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _19j=B(A(_13U,[_])),_19k=E(_19j);if(!_19k[0]){var _19l=B(_Yd(_Ys,_17f,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _19m=function(_19n,_){var _19o=E(_19n),_19p=toJSStr(_18m),_19q=E(_16l)(_19p),_19r=B(A(_5,[_6R,new T(function(){var _19s=String(_19q);return fromJSStr(_19s);}),_])),_=wMV(_190,_19r),_19t=E(_16k)(_19p),_19u=new T(function(){var _19v=String(_19t);return fromJSStr(_19v);}),_=wMV(_192,_19u),_19w=B(_Yt(_11m,_18j,new T(function(){return B(_16(_19u,_18l));},1),_)),_19x=B(_Yt(_11n,_18j,new T(function(){return B(_16(_19u,_18k));},1),_));return new F(function(){return _12x(_18X,_18V,_190,_);});},_19y=B(A(_xD,[_6S,_S,_o,_19h[1],_wH,_19m,_])),_19z=B(A(_xD,[_6S,_S,_o,_19k[1],_wH,_13I,_])),_19A=B(A(_Y2,[_6R,_18i,_])),_19B=E(_19A);if(!_19B[0]){var _19C=B(_Yd(_Ys,_17f,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _19D=_19B[1],_19E=B(A(_13S,[_])),_19F=E(_19E);if(!_19F[0]){var _19G=B(_Yd(_Ys,_17f,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _19H=_19F[1],_19I=B(A(_Y2,[_6R,_11v,_])),_19J=E(_19I);if(!_19J[0]){var _19K=B(_Yd(_Ys,_17f,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _19L=E(_19J[1]),_19M=E(_N),_19N=_19M(_19L);if(!_19N){var _19O=B(_Yd(_Ys,_17f,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _19P=E(_M),_19Q=_19P(_19L),_19R=_19Q,_19S=B(A(_Y2,[_6R,_11q,_])),_19T=function(_,_19U){var _19V=E(_19U);if(!_19V[0]){var _19W=B(_Yd(_Ys,_17f,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _19X=function(_){return new F(function(){return _12x(_18X,_18V,_190,_);});},_19Y=B(_14u(_18V,[0,_19R,_19L],_19X,_)),_19Z=B(_15H(_18X,_19V[1],_19X,_)),_1a0=B(A(_13L,[_])),_1a1=E(_1a0);if(!_1a1[0]){var _1a2=B(_Yd(_Ys,_17f,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1a3=_1a1[1],_1a4=B(A(_13D,[_])),_1a5=E(_1a4);if(!_1a5[0]){var _1a6=B(_Yd(_Ys,_17f,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1a7=_1a5[1],_1a8=B(A(_13B,[_])),_1a9=E(_1a8);if(!_1a9[0]){var _1aa=B(_Yd(_Ys,_17f,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1ab=_1a9[1],_1ac=function(_){var _1ad=B(_13N(_18h,_)),_1ae=E(_1ad);if(!_1ae[0]){var _1af=B(_Yd(_Ys,_17t,_)),_1ag=B(_13N(_17q,_)),_1ah=function(_,_1ai){var _1aj=function(_,_1ak){var _1al=function(_){var _1am=B(_13N(_17m,_)),_1an=function(_,_1ao){var _1ap=E(_1ao);if(!_1ap[0]){var _1aq=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1ar=B(_13N(_17l,_)),_1as=E(_1ar);if(!_1as[0]){var _1at=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1au=B(_185(_qM,_1as[1]));if(!_1au[0]){var _1av=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1aw=B(_13N(_17k,_)),_1ax=E(_1aw);if(!_1ax[0]){var _1ay=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1az=B(_185(_qM,_1ax[1]));if(!_1az[0]){var _1aA=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1aB=B(A(_16e,[_st,_165,_17j,_])),_1aC=function(_,_1aD){var _1aE=E(_1aD);if(!_1aE[0]){var _1aF=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1aG=B(A(_121,[_S,_st,_1aE[1],_13M,_])),_1aH=E(_1aG);if(!_1aH[0]){var _1aI=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1aJ=B(_185(_ro,_1aH[1]));if(!_1aJ[0]){var _1aK=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1aL=rMV(_18X),_1aM=E(_1aL),_=wMV(_18X,[0,_1aM[1],_1aM[2],_1ap[1],_1au[1],_1az[1],_1aJ[1],_1aM[7],_1aM[8]]);return new F(function(){return _12x(_18X,_18V,_190,_);});}}}},_1aN=E(_1aB);if(!_1aN[0]){return new F(function(){return _1aC(_,_6J);});}else{var _1aO=E(_1aN[1]);if(!_1aO[0]){return new F(function(){return _1aC(_,_6J);});}else{return new F(function(){return _1aC(_,[1,_1aO[1]]);});}}}}}}}},_1aP=E(_1am);if(!_1aP[0]){return new F(function(){return _1an(_,_6J);});}else{var _1aQ=B(_185(_qM,_1aP[1]));if(!_1aQ[0]){return new F(function(){return _1an(_,_6J);});}else{return new F(function(){return _1an(_,[1,_1aQ[1]]);});}}};if(!E(_1ak)[0]){var _1aR=B(_Yd(_Ys,_17p,_));return new F(function(){return _1al(_);});}else{return new F(function(){return _1al(_);});}},_1aS=E(_1ai);if(!_1aS[0]){return new F(function(){return _1aj(_,_6J);});}else{var _1aT=rMV(_18X),_1aU=E(_1aT),_=wMV(_18X,[0,_1aU[1],_1aU[2],_1aU[3],_1aU[4],_1aU[5],_1aU[6],_1aS[1],_1aU[8]]);return new F(function(){return _1aj(_,_17c);});}},_1aV=E(_1ag);if(!_1aV[0]){return new F(function(){return _1ah(_,_6J);});}else{var _1aW=B(_185(_qM,_1aV[1]));if(!_1aW[0]){return new F(function(){return _1ah(_,_6J);});}else{return new F(function(){return _1ah(_,[1,_1aW[1]]);});}}}else{var _1aX=function(_,_1aY){var _1aZ=function(_){var _1b0=B(_13N(_17q,_)),_1b1=function(_,_1b2){var _1b3=function(_,_1b4){var _1b5=function(_){var _1b6=B(_13N(_17m,_)),_1b7=function(_,_1b8){var _1b9=E(_1b8);if(!_1b9[0]){var _1ba=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1bb=B(_13N(_17l,_)),_1bc=E(_1bb);if(!_1bc[0]){var _1bd=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1be=B(_185(_qM,_1bc[1]));if(!_1be[0]){var _1bf=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1bg=B(_13N(_17k,_)),_1bh=E(_1bg);if(!_1bh[0]){var _1bi=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1bj=B(_185(_qM,_1bh[1]));if(!_1bj[0]){var _1bk=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1bl=B(A(_16e,[_st,_165,_17j,_])),_1bm=function(_,_1bn){var _1bo=E(_1bn);if(!_1bo[0]){var _1bp=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1bq=B(A(_121,[_S,_st,_1bo[1],_13M,_])),_1br=E(_1bq);if(!_1br[0]){var _1bs=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1bt=B(_185(_ro,_1br[1]));if(!_1bt[0]){var _1bu=B(_Yd(_Ys,_17i,_));return new F(function(){return _12x(_18X,_18V,_190,_);});}else{var _1bv=rMV(_18X),_1bw=E(_1bv),_=wMV(_18X,[0,_1bw[1],_1bw[2],_1b9[1],_1be[1],_1bj[1],_1bt[1],_1bw[7],_1bw[8]]);return new F(function(){return _12x(_18X,_18V,_190,_);});}}}},_1bx=E(_1bl);if(!_1bx[0]){return new F(function(){return _1bm(_,_6J);});}else{var _1by=E(_1bx[1]);if(!_1by[0]){return new F(function(){return _1bm(_,_6J);});}else{return new F(function(){return _1bm(_,[1,_1by[1]]);});}}}}}}}},_1bz=E(_1b6);if(!_1bz[0]){return new F(function(){return _1b7(_,_6J);});}else{var _1bA=B(_185(_qM,_1bz[1]));if(!_1bA[0]){return new F(function(){return _1b7(_,_6J);});}else{return new F(function(){return _1b7(_,[1,_1bA[1]]);});}}};if(!E(_1b4)[0]){var _1bB=B(_Yd(_Ys,_17p,_));return new F(function(){return _1b5(_);});}else{return new F(function(){return _1b5(_);});}},_1bC=E(_1b2);if(!_1bC[0]){return new F(function(){return _1b3(_,_6J);});}else{var _1bD=rMV(_18X),_1bE=E(_1bD),_=wMV(_18X,[0,_1bE[1],_1bE[2],_1bE[3],_1bE[4],_1bE[5],_1bE[6],_1bC[1],_1bE[8]]);return new F(function(){return _1b3(_,_17c);});}},_1bF=E(_1b0);if(!_1bF[0]){return new F(function(){return _1b1(_,_6J);});}else{var _1bG=B(_185(_qM,_1bF[1]));if(!_1bG[0]){return new F(function(){return _1b1(_,_6J);});}else{return new F(function(){return _1b1(_,[1,_1bG[1]]);});}}};if(!E(_1aY)[0]){var _1bH=B(_Yd(_Ys,_17t,_));return new F(function(){return _1aZ(_);});}else{return new F(function(){return _1aZ(_);});}},_1bI=B(_18K(_18b,_18g,_1ae[1]));if(!_1bI[0]){return new F(function(){return _1aX(_,_6J);});}else{var _1bJ=rMV(_18X),_1bK=E(_1bJ),_=wMV(_18X,[0,_1bK[1],_1bK[2],_1bK[3],_1bK[4],_1bK[5],_1bK[6],_1bK[7],new T(function(){return B(_bc(_18u,_1bI[1]));})]);return new F(function(){return _1aX(_,_17c);});}}},_1bL=function(_1bM,_){return new F(function(){return _1ac(_);});},_1bN=function(_1bO,_){while(1){var _1bP=E(_1bO);if(!_1bP[0]){var _1bQ=B(A(_xD,[_6S,_S,_o,_19H,_wH,_1bL,_])),_1bR=B(A(_xD,[_6S,_S,_o,_19D,_wH,_1bL,_])),_1bS=B(A(_xD,[_6S,_S,_o,_1a3,_wH,_1bL,_])),_1bT=B(A(_xD,[_6S,_S,_o,_1a7,_wH,_1bL,_])),_1bU=B(A(_xD,[_6S,_S,_o,_1ab,_wH,_1bL,_]));return _a;}else{var _1bV=B(A(_xD,[_6S,_S,_o,_1bP[1],_wH,_1bL,_]));_1bO=_1bP[2];continue;}}},_1bW=B(_1bN(_194,_)),_1bX=B(A(_xD,[_6S,_S,_L,_19H,_13z,_1bL,_])),_1bY=B(A(_xD,[_6S,_S,_L,_19D,_13z,_1bL,_])),_1bZ=B(A(_xD,[_6S,_S,_L,_1a3,_13z,_1bL,_])),_1c0=B(A(_xD,[_6S,_S,_L,_1a7,_13z,_1bL,_])),_1c1=B(A(_xD,[_6S,_S,_L,_1ab,_13z,_1bL,_]));return new F(function(){return _12x(_18X,_18V,_190,_);});}}}}},_1c2=E(_19S);if(!_1c2[0]){return new F(function(){return _19T(_,_6J);});}else{var _1c3=E(_1c2[1]),_1c4=_19M(_1c3);if(!_1c4){return new F(function(){return _19T(_,_6J);});}else{var _1c5=_19P(_1c3);return new F(function(){return _19T(_,[1,[0,_1c5,_1c3]]);});}}}}}}}}},_1c6=function(_){return new F(function(){return _18T(_);});};
var hasteMain = function() {B(A(_1c6, [0]));};window.onload = hasteMain;