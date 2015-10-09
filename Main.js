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

var _0="src",_1=(function(e,p,v){e[p] = v;}),_2=function(_3){return E(E(_3)[2]);},_4=(function(t){return document.createElement(t);}),_5=function(_6,_7){return new F(function(){return A(_2,[_6,function(_){var _8=E(_4)("img"),_9=E(_1)(_8,E(_0),toJSStr(E(_7)));return _8;}]);});},_a=0,_b=function(_){return _a;},_c=function(_d,_e,_){return new F(function(){return _b(_);});},_f="scroll",_g="submit",_h="blur",_i="focus",_j="change",_k="unload",_l="load",_m=function(_n){switch(E(_n)){case 0:return E(_l);case 1:return E(_k);case 2:return E(_j);case 3:return E(_i);case 4:return E(_h);case 5:return E(_g);default:return E(_f);}},_o=[0,_m,_c],_p="metaKey",_q="shiftKey",_r="altKey",_s="ctrlKey",_t="keyCode",_u=function(_v,_){var _w=_v[E(_t)],_x=_v[E(_s)],_y=_v[E(_r)],_z=_v[E(_q)],_A=_v[E(_p)];return new T(function(){var _B=Number(_w),_C=jsTrunc(_B);return [0,_C,E(_x),E(_y),E(_z),E(_A)];});},_D=function(_E,_F,_){return new F(function(){return _u(E(_F),_);});},_G="keydown",_H="keyup",_I="keypress",_J=function(_K){switch(E(_K)){case 0:return E(_I);case 1:return E(_H);default:return E(_G);}},_L=[0,_J,_D],_M=(function(e){return e.getContext('2d');}),_N=(function(e){return !!e.getContext;}),_O=function(_P,_){return [1,_P];},_Q=function(_R){return E(_R);},_S=[0,_Q,_O],_T=function(_U){return E(E(_U)[1]);},_V=function(_W,_X){return (!B(A(_T,[_Y,_W,_X])))?true:false;},_Z=function(_10,_11){var _12=strEq(E(_10),E(_11));return (E(_12)==0)?false:true;},_13=function(_14,_15){return new F(function(){return _Z(_14,_15);});},_Y=new T(function(){return [0,_13,_V];}),_16=function(_17,_18){var _19=E(_17);return (_19[0]==0)?E(_18):[1,_19[1],new T(function(){return B(_16(_19[2],_18));})];},_1a=new T(function(){return B(unCStr("!!: negative index"));}),_1b=new T(function(){return B(unCStr("Prelude."));}),_1c=new T(function(){return B(_16(_1b,_1a));}),_1d=new T(function(){return B(err(_1c));}),_1e=new T(function(){return B(unCStr("!!: index too large"));}),_1f=new T(function(){return B(_16(_1b,_1e));}),_1g=new T(function(){return B(err(_1f));}),_1h=function(_1i,_1j){while(1){var _1k=E(_1i);if(!_1k[0]){return E(_1g);}else{var _1l=E(_1j);if(!_1l){return E(_1k[1]);}else{_1i=_1k[2];_1j=_1l-1|0;continue;}}}},_1m=function(_1n,_1o){if(_1o>=0){return new F(function(){return _1h(_1n,_1o);});}else{return E(_1d);}},_1p=new T(function(){return B(unCStr(": empty list"));}),_1q=function(_1r){return new F(function(){return err(B(_16(_1b,new T(function(){return B(_16(_1r,_1p));},1))));});},_1s=new T(function(){return B(unCStr("head"));}),_1t=new T(function(){return B(_1q(_1s));}),_1u=function(_1v){var _1w=E(_1v);if(_1w[0]==3){var _1x=E(_1w[1]);if(!_1x[0]){return E(_1t);}else{var _1y=E(_1x[1]);if(!_1y[0]){var _1z=B(_1m(_1x,1));return (_1z[0]==0)?[1,[0,_1y[1],_1z[1]]]:[0];}else{return [0];}}}else{return [0];}},_1A=function(_1B,_1C){var _1D=E(_1C);return (_1D[0]==0)?[0]:[1,new T(function(){return B(A(_1B,[_1D[1]]));}),new T(function(){return B(_1A(_1B,_1D[2]));})];},_1E=function(_1F){var _1G=E(_1F);if(_1G[0]==3){var _1H=B(_1A(_1u,_1G[1]));if(!_1H[0]){return E(_1t);}else{var _1I=E(_1H[1]);if(!_1I[0]){return [0];}else{var _1J=B(_1m(_1H,1));if(!_1J[0]){return [0];}else{var _1K=B(_1m(_1H,2));if(!_1K[0]){return [0];}else{var _1L=B(_1m(_1H,3));return (_1L[0]==0)?[0]:[1,[0,_1I[1],_1J[1],_1K[1],_1L[1]]];}}}}}else{return [0];}},_1M="box",_1N="mouse",_1O="corner",_1P="Dragging",_1Q=[0],_1R=[1,_1Q],_1S="Free",_1T="state",_1U=1,_1V=[1,_1U],_1W=0,_1X=[1,_1W],_1Y=3,_1Z=[1,_1Y],_20=2,_21=[1,_20],_22=new T(function(){return B(unCStr("SW"));}),_23=new T(function(){return B(unCStr("SE"));}),_24=new T(function(){return B(unCStr("NW"));}),_25=new T(function(){return B(unCStr("NE"));}),_26=function(_27,_28){while(1){var _29=E(_27);if(!_29[0]){return (E(_28)[0]==0)?true:false;}else{var _2a=E(_28);if(!_2a[0]){return false;}else{if(E(_29[1])!=E(_2a[1])){return false;}else{_27=_29[2];_28=_2a[2];continue;}}}}},_2b=function(_2c){var _2d=E(_2c);if(_2d[0]==1){var _2e=fromJSStr(_2d[1]);return (!B(_26(_2e,_25)))?(!B(_26(_2e,_24)))?(!B(_26(_2e,_23)))?(!B(_26(_2e,_22)))?[0]:E(_21):E(_1Z):E(_1X):E(_1V);}else{return [0];}},_2f=function(_2g,_2h,_2i){while(1){var _2j=E(_2i);if(!_2j[0]){return [0];}else{var _2k=E(_2j[1]);if(!B(A(_T,[_2g,_2h,_2k[1]]))){_2i=_2j[2];continue;}else{return [1,_2k[2]];}}}},_2l=function(_2m){var _2n=E(_2m);if(_2n[0]==4){var _2o=_2n[1],_2p=B(_2f(_Y,_1T,_2o));if(!_2p[0]){return [0];}else{var _2q=E(_2p[1]);if(_2q[0]==1){var _2r=_2q[1],_2s=strEq(_2r,E(_1S));if(!E(_2s)){var _2t=strEq(_2r,E(_1P));if(!E(_2t)){return [0];}else{var _2u=B(_2f(_Y,_1O,_2o));if(!_2u[0]){return [0];}else{var _2v=B(_2b(_2u[1]));return (_2v[0]==0)?[0]:[1,[1,_2v[1]]];}}}else{return E(_1R);}}else{return [0];}}}else{return [0];}},_2w=function(_2x){var _2y=E(_2x);if(_2y[0]==4){var _2z=_2y[1],_2A=B(_2f(_Y,_1N,_2z));if(!_2A[0]){return [0];}else{var _2B=B(_2l(_2A[1]));if(!_2B[0]){return [0];}else{var _2C=B(_2f(_Y,_1M,_2z));if(!_2C[0]){return [0];}else{var _2D=B(_1E(_2C[1]));return (_2D[0]==0)?[0]:[1,[0,_2B[1],_2D[1]]];}}}}else{return [0];}},_2E=function(_2F){return [0,E(_2F)];},_2G=function(_2H){var _2I=E(_2H);return (_2I[0]==0)?[1,_2I[1]]:[0];},_2J=[0,_2E,_2G],_2K=1,_2L=[1,_2K],_2M=0,_2N=[1,_2M],_2O=new T(function(){return B(unCStr("Top"));}),_2P=new T(function(){return B(unCStr("Bottom"));}),_2Q=function(_2R){var _2S=E(_2R);if(_2S[0]==1){var _2T=fromJSStr(_2S[1]);return (!B(_26(_2T,_2P)))?(!B(_26(_2T,_2O)))?[0]:E(_2N):E(_2L);}else{return [0];}},_2U=1,_2V=[1,_2U],_2W=0,_2X=[1,_2W],_2Y=new T(function(){return B(unCStr("Free"));}),_2Z=new T(function(){return B(unCStr("Dragging"));}),_30=function(_31){var _32=E(_31);if(_32[0]==1){var _33=fromJSStr(_32[1]);return (!B(_26(_33,_2Z)))?(!B(_26(_33,_2Y)))?[0]:E(_2X):E(_2V);}else{return [0];}},_34="title",_35="points",_36=function(_37){var _38=E(_37);if(_38[0]==4){var _39=_38[1],_3a=B(_2f(_Y,_35,_39));if(!_3a[0]){return [0];}else{var _3b=E(_3a[1]);if(_3b[0]==3){var _3c=E(_3b[1]);if(!_3c[0]){return E(_1t);}else{var _3d=E(_3c[1]);if(_3d[0]==3){var _3e=E(_3d[1]);if(!_3e[0]){return E(_1t);}else{var _3f=E(_3e[1]);if(!_3f[0]){var _3g=B(_1m(_3e,1));if(!_3g[0]){var _3h=B(_1m(_3c,1));if(_3h[0]==3){var _3i=E(_3h[1]);if(!_3i[0]){return E(_1t);}else{var _3j=E(_3i[1]);if(!_3j[0]){var _3k=B(_1m(_3i,1));if(!_3k[0]){var _3l=B(_2f(_Y,_34,_39));if(!_3l[0]){return [0];}else{var _3m=E(_3l[1]);return (_3m[0]==1)?[1,[0,[0,_3f[1],_3g[1]],[0,_3j[1],_3k[1]],new T(function(){return fromJSStr(_3m[1]);})]]:[0];}}else{return [0];}}else{return [0];}}}else{return [0];}}else{return [0];}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}},_3n=[0],_3o=function(_3p){var _3q=new T(function(){var _3r=E(E(_3p)[2]);return [3,[1,new T(function(){return B(_2E(_3r[1]));}),[1,new T(function(){return B(_2E(_3r[2]));}),_3n]]];}),_3s=new T(function(){var _3t=E(E(_3p)[1]);return [3,[1,new T(function(){return B(_2E(_3t[1]));}),[1,new T(function(){return B(_2E(_3t[2]));}),_3n]]];});return [1,[0,_34,new T(function(){return [1,toJSStr(E(E(_3p)[3]))];})],[1,[0,_35,[3,[1,_3s,[1,_3q,_3n]]]],_3n]];},_3u=function(_3v){return [4,E(B(_3o(_3v)))];},_3w=[0,_3u,_36],_3x="rotations",_3y="choice",_3z="offset",_3A="bottom",_3B="top",_3C="fileName",_3D="scans",_3E="mouse",_3F=[1,_3n],_3G=function(_3H){return E(E(_3H)[2]);},_3I=function(_3J,_3K){var _3L=E(_3K);if(_3L[0]==3){var _3M=new T(function(){return B(_3G(_3J));}),_3N=function(_3O){var _3P=E(_3O);if(!_3P[0]){return E(_3F);}else{var _3Q=B(A(_3M,[_3P[1]]));if(!_3Q[0]){return [0];}else{var _3R=B(_3N(_3P[2]));return (_3R[0]==0)?[0]:[1,[1,_3Q[1],_3R[1]]];}}};return new F(function(){return _3N(_3L[1]);});}else{return [0];}},_3S=function(_3T){var _3U=E(_3T);if(_3U[0]==4){var _3V=_3U[1],_3W=B(_2f(_Y,_3E,_3V));if(!_3W[0]){return [0];}else{var _3X=B(_30(_3W[1]));if(!_3X[0]){return [0];}else{var _3Y=B(_2f(_Y,_3D,_3V));if(!_3Y[0]){return [0];}else{var _3Z=B(_3I(_3w,_3Y[1]));if(!_3Z[0]){return [0];}else{var _40=B(_2f(_Y,_3C,_3V));if(!_40[0]){return [0];}else{var _41=E(_40[1]);if(_41[0]==1){var _42=B(_2f(_Y,_3B,_3V));if(!_42[0]){return [0];}else{var _43=E(_42[1]);if(!_43[0]){var _44=B(_2f(_Y,_3A,_3V));if(!_44[0]){return [0];}else{var _45=E(_44[1]);if(!_45[0]){var _46=B(_2f(_Y,_3z,_3V));if(!_46[0]){return [0];}else{var _47=E(_46[1]);if(!_47[0]){var _48=B(_2f(_Y,_3y,_3V));if(!_48[0]){return [0];}else{var _49=B(_2Q(_48[1]));if(!_49[0]){return [0];}else{var _4a=B(_2f(_Y,_3x,_3V));if(!_4a[0]){return [0];}else{var _4b=B(_3I(_2J,_4a[1]));return (_4b[0]==0)?[0]:[1,[0,_3X[1],_3Z[1],new T(function(){return fromJSStr(_41[1]);}),_43[1],_45[1],_47[1],_49[1],_4b[1]]];}}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}}}}}else{return [0];}},_4c="scans",_4d="calib",_4e=function(_4f){var _4g=E(_4f);if(_4g[0]==4){var _4h=_4g[1],_4i=B(_2f(_Y,_4d,_4h));if(!_4i[0]){return [0];}else{var _4j=B(_2w(_4i[1]));if(!_4j[0]){return [0];}else{var _4k=B(_2f(_Y,_4c,_4h));if(!_4k[0]){return [0];}else{var _4l=B(_3S(_4k[1]));return (_4l[0]==0)?[0]:[1,[0,_4j[1],_4l[1]]];}}}}else{return [0];}},_4m=function(_4n,_4o,_){var _4p=B(A(_4n,[_])),_4q=B(A(_4o,[_]));return _4p;},_4r=function(_4s,_4t,_){var _4u=B(A(_4s,[_])),_4v=B(A(_4t,[_]));return new T(function(){return B(A(_4u,[_4v]));});},_4w=function(_4x,_4y,_){var _4z=B(A(_4y,[_]));return _4x;},_4A=function(_4B,_4C,_){var _4D=B(A(_4C,[_]));return new T(function(){return B(A(_4B,[_4D]));});},_4E=[0,_4A,_4w],_4F=function(_4G,_){return _4G;},_4H=function(_4I,_4J,_){var _4K=B(A(_4I,[_]));return new F(function(){return A(_4J,[_]);});},_4L=[0,_4E,_4F,_4r,_4H,_4m],_4M=function(_4N,_4O,_){var _4P=B(A(_4N,[_]));return new F(function(){return A(_4O,[_4P,_]);});},_4Q=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_4R=new T(function(){return B(unCStr("base"));}),_4S=new T(function(){return B(unCStr("IOException"));}),_4T=new T(function(){var _4U=hs_wordToWord64(4053623282),_4V=hs_wordToWord64(3693590983);return [0,_4U,_4V,[0,_4U,_4V,_4R,_4Q,_4S],_3n,_3n];}),_4W=function(_4X){return E(_4T);},_4Y=function(_4Z){return E(E(_4Z)[1]);},_50=function(_51,_52,_53){var _54=B(A(_51,[_])),_55=B(A(_52,[_])),_56=hs_eqWord64(_54[1],_55[1]);if(!_56){return [0];}else{var _57=hs_eqWord64(_54[2],_55[2]);return (!_57)?[0]:[1,_53];}},_58=function(_59){var _5a=E(_59);return new F(function(){return _50(B(_4Y(_5a[1])),_4W,_5a[2]);});},_5b=new T(function(){return B(unCStr(": "));}),_5c=new T(function(){return B(unCStr(")"));}),_5d=new T(function(){return B(unCStr(" ("));}),_5e=new T(function(){return B(unCStr("interrupted"));}),_5f=new T(function(){return B(unCStr("system error"));}),_5g=new T(function(){return B(unCStr("unsatisified constraints"));}),_5h=new T(function(){return B(unCStr("user error"));}),_5i=new T(function(){return B(unCStr("permission denied"));}),_5j=new T(function(){return B(unCStr("illegal operation"));}),_5k=new T(function(){return B(unCStr("end of file"));}),_5l=new T(function(){return B(unCStr("resource exhausted"));}),_5m=new T(function(){return B(unCStr("resource busy"));}),_5n=new T(function(){return B(unCStr("does not exist"));}),_5o=new T(function(){return B(unCStr("already exists"));}),_5p=new T(function(){return B(unCStr("resource vanished"));}),_5q=new T(function(){return B(unCStr("timeout"));}),_5r=new T(function(){return B(unCStr("unsupported operation"));}),_5s=new T(function(){return B(unCStr("hardware fault"));}),_5t=new T(function(){return B(unCStr("inappropriate type"));}),_5u=new T(function(){return B(unCStr("invalid argument"));}),_5v=new T(function(){return B(unCStr("failed"));}),_5w=new T(function(){return B(unCStr("protocol error"));}),_5x=function(_5y,_5z){switch(E(_5y)){case 0:return new F(function(){return _16(_5o,_5z);});break;case 1:return new F(function(){return _16(_5n,_5z);});break;case 2:return new F(function(){return _16(_5m,_5z);});break;case 3:return new F(function(){return _16(_5l,_5z);});break;case 4:return new F(function(){return _16(_5k,_5z);});break;case 5:return new F(function(){return _16(_5j,_5z);});break;case 6:return new F(function(){return _16(_5i,_5z);});break;case 7:return new F(function(){return _16(_5h,_5z);});break;case 8:return new F(function(){return _16(_5g,_5z);});break;case 9:return new F(function(){return _16(_5f,_5z);});break;case 10:return new F(function(){return _16(_5w,_5z);});break;case 11:return new F(function(){return _16(_5v,_5z);});break;case 12:return new F(function(){return _16(_5u,_5z);});break;case 13:return new F(function(){return _16(_5t,_5z);});break;case 14:return new F(function(){return _16(_5s,_5z);});break;case 15:return new F(function(){return _16(_5r,_5z);});break;case 16:return new F(function(){return _16(_5q,_5z);});break;case 17:return new F(function(){return _16(_5p,_5z);});break;default:return new F(function(){return _16(_5e,_5z);});}},_5A=new T(function(){return B(unCStr("}"));}),_5B=new T(function(){return B(unCStr("{handle: "));}),_5C=function(_5D,_5E,_5F,_5G,_5H,_5I){var _5J=new T(function(){var _5K=new T(function(){var _5L=new T(function(){var _5M=E(_5G);if(!_5M[0]){return E(_5I);}else{var _5N=new T(function(){return B(_16(_5M,new T(function(){return B(_16(_5c,_5I));},1)));},1);return B(_16(_5d,_5N));}},1);return B(_5x(_5E,_5L));}),_5O=E(_5F);if(!_5O[0]){return E(_5K);}else{return B(_16(_5O,new T(function(){return B(_16(_5b,_5K));},1)));}}),_5P=E(_5H);if(!_5P[0]){var _5Q=E(_5D);if(!_5Q[0]){return E(_5J);}else{var _5R=E(_5Q[1]);if(!_5R[0]){var _5S=new T(function(){var _5T=new T(function(){return B(_16(_5A,new T(function(){return B(_16(_5b,_5J));},1)));},1);return B(_16(_5R[1],_5T));},1);return new F(function(){return _16(_5B,_5S);});}else{var _5U=new T(function(){var _5V=new T(function(){return B(_16(_5A,new T(function(){return B(_16(_5b,_5J));},1)));},1);return B(_16(_5R[1],_5V));},1);return new F(function(){return _16(_5B,_5U);});}}}else{return new F(function(){return _16(_5P[1],new T(function(){return B(_16(_5b,_5J));},1));});}},_5W=function(_5X){var _5Y=E(_5X);return new F(function(){return _5C(_5Y[1],_5Y[2],_5Y[3],_5Y[4],_5Y[6],_3n);});},_5Z=function(_60,_61,_62){var _63=E(_61);return new F(function(){return _5C(_63[1],_63[2],_63[3],_63[4],_63[6],_62);});},_64=function(_65,_66){var _67=E(_65);return new F(function(){return _5C(_67[1],_67[2],_67[3],_67[4],_67[6],_66);});},_68=44,_69=93,_6a=91,_6b=function(_6c,_6d,_6e){var _6f=E(_6d);if(!_6f[0]){return new F(function(){return unAppCStr("[]",_6e);});}else{var _6g=new T(function(){var _6h=new T(function(){var _6i=function(_6j){var _6k=E(_6j);if(!_6k[0]){return [1,_69,_6e];}else{var _6l=new T(function(){return B(A(_6c,[_6k[1],new T(function(){return B(_6i(_6k[2]));})]));});return [1,_68,_6l];}};return B(_6i(_6f[2]));});return B(A(_6c,[_6f[1],_6h]));});return [1,_6a,_6g];}},_6m=function(_6n,_6o){return new F(function(){return _6b(_64,_6n,_6o);});},_6p=[0,_5Z,_5W,_6m],_6q=new T(function(){return [0,_4W,_6p,_6r,_58,_5W];}),_6r=function(_6s){return [0,_6q,_6s];},_6t=[0],_6u=7,_6v=function(_6w){return [0,_6t,_6u,_3n,_6w,_6t,_6t];},_6x=function(_6y,_){var _6z=new T(function(){return B(_6r(new T(function(){return B(_6v(_6y));})));});return new F(function(){return die(_6z);});},_6A=[0,_4L,_4M,_4H,_4F,_6x],_6B=[0,_6A,_Q],_6C=[0,_6B,_4F],_6D=function(_6E,_6F,_6G,_6H,_6I,_6J,_6K,_6L){if(_6E!=_6I){return false;}else{if(E(_6F)!=E(_6J)){return false;}else{var _6M=E(_6G),_6N=E(_6K);if(E(_6M[1])!=E(_6N[1])){return false;}else{if(E(_6M[2])!=E(_6N[2])){return false;}else{return new F(function(){return _26(_6H,_6L);});}}}}},_6O=function(_6P,_6Q){var _6R=E(_6P),_6S=E(_6R[1]),_6T=E(_6Q),_6U=E(_6T[1]);return new F(function(){return _6D(E(_6S[1]),_6S[2],_6R[2],_6R[3],E(_6U[1]),_6U[2],_6T[2],_6T[3]);});},_6V="scans",_6W=[1,_6V,_3n],_6X="calib",_6Y=[1,_6X,_6W],_6Z=function(_70){var _71=E(_70);return [3,[1,new T(function(){return B(_2E(_71[1]));}),[1,new T(function(){return B(_2E(_71[2]));}),_3n]]];},_72=new T(function(){return [1,"Dragging"];}),_73=[0,_1T,_72],_74=new T(function(){return [1,"Free"];}),_75="state",_76=[0,_75,_74],_77=[1,_76,_3n],_78=[4,E(_77)],_79=function(_7a,_7b){switch(E(_7a)){case 0:return new F(function(){return _16(_24,_7b);});break;case 1:return new F(function(){return _16(_25,_7b);});break;case 2:return new F(function(){return _16(_22,_7b);});break;default:return new F(function(){return _16(_23,_7b);});}},_7c=function(_7d){return E(toJSStr(B(_79(_7d,_3n))));},_7e=function(_7f){return [1,B(_7c(_7f))];},_7g=function(_7h){var _7i=new T(function(){var _7j=E(E(_7h)[2]);return [3,[1,new T(function(){return B(_6Z(_7j[1]));}),[1,new T(function(){return B(_6Z(_7j[2]));}),[1,new T(function(){return B(_6Z(_7j[3]));}),[1,new T(function(){return B(_6Z(_7j[4]));}),_3n]]]]];}),_7k=new T(function(){var _7l=E(E(_7h)[1]);if(!_7l[0]){return E(_78);}else{return [4,[1,_73,[1,[0,_1O,new T(function(){return B(_7e(_7l[1]));})],_3n]]];}});return [1,[0,_1N,_7k],[1,[0,_1M,_7i],_3n]];},_7m="rotations",_7n=[1,_7m,_3n],_7o="choice",_7p=[1,_7o,_7n],_7q="offset",_7r=[1,_7q,_7p],_7s="bottom",_7t=[1,_7s,_7r],_7u="top",_7v=[1,_7u,_7t],_7w="fileName",_7x=[1,_7w,_7v],_7y="scans",_7z=[1,_7y,_7x],_7A="mouse",_7B=[1,_7A,_7z],_7C=function(_7D,_7E){var _7F=E(_7D);if(!_7F[0]){return [0];}else{var _7G=E(_7E);return (_7G[0]==0)?[0]:[1,[0,_7F[1],_7G[1]],new T(function(){return B(_7C(_7F[2],_7G[2]));})];}},_7H=function(_7I){return new F(function(){return _7C(_7B,[1,new T(function(){if(!E(E(_7I)[1])){return [1,toJSStr(E(_2Y))];}else{return [1,toJSStr(E(_2Z))];}}),[1,new T(function(){return [3,E(B(_1A(_3u,E(_7I)[2])))];}),[1,new T(function(){return [1,toJSStr(E(E(_7I)[3]))];}),[1,new T(function(){return [0,E(E(_7I)[4])];}),[1,new T(function(){return [0,E(E(_7I)[5])];}),[1,new T(function(){return [0,E(E(_7I)[6])];}),[1,new T(function(){if(!E(E(_7I)[7])){return [1,toJSStr(E(_2O))];}else{return [1,toJSStr(E(_2P))];}}),[1,new T(function(){return [3,E(B(_1A(_2E,E(_7I)[8])))];}),_3n]]]]]]]]);});},_7J=function(_7K){return [1,E(_7K)];},_7L="deltaZ",_7M="deltaY",_7N="deltaX",_7O=function(_7P,_7Q){var _7R=jsShowI(_7P);return new F(function(){return _16(fromJSStr(_7R),_7Q);});},_7S=41,_7T=40,_7U=function(_7V,_7W,_7X){if(_7W>=0){return new F(function(){return _7O(_7W,_7X);});}else{if(_7V<=6){return new F(function(){return _7O(_7W,_7X);});}else{return [1,_7T,new T(function(){var _7Y=jsShowI(_7W);return B(_16(fromJSStr(_7Y),[1,_7S,_7X]));})];}}},_7Z=new T(function(){return B(unCStr(")"));}),_80=new T(function(){return B(_7U(0,2,_7Z));}),_81=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_80));}),_82=function(_83){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_7U(0,_83,_81));}))));});},_84=function(_85,_){return new T(function(){var _86=Number(E(_85)),_87=jsTrunc(_86);if(_87<0){return B(_82(_87));}else{if(_87>2){return B(_82(_87));}else{return _87;}}});},_88=0,_89=[0,_88,_88,_88],_8a="button",_8b=new T(function(){return jsGetMouseCoords;}),_8c=function(_8d,_){var _8e=E(_8d);if(!_8e[0]){return _3n;}else{var _8f=B(_8c(_8e[2],_));return [1,new T(function(){var _8g=Number(E(_8e[1]));return jsTrunc(_8g);}),_8f];}},_8h=function(_8i,_){var _8j=__arr2lst(0,_8i);return new F(function(){return _8c(_8j,_);});},_8k=function(_8l,_){return new F(function(){return _8h(E(_8l),_);});},_8m=function(_8n,_){return new T(function(){var _8o=Number(E(_8n));return jsTrunc(_8o);});},_8p=[0,_8m,_8k],_8q=function(_8r,_){var _8s=E(_8r);if(!_8s[0]){return _3n;}else{var _8t=B(_8q(_8s[2],_));return [1,_8s[1],_8t];}},_8u=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_8v=[0,_6t,_6u,_3n,_8u,_6t,_6t],_8w=new T(function(){return B(_6r(_8v));}),_8x=function(_){return new F(function(){return die(_8w);});},_8y=function(_8z){return E(E(_8z)[1]);},_8A=function(_8B,_8C,_8D,_){var _8E=__arr2lst(0,_8D),_8F=B(_8q(_8E,_)),_8G=E(_8F);if(!_8G[0]){return new F(function(){return _8x(_);});}else{var _8H=E(_8G[2]);if(!_8H[0]){return new F(function(){return _8x(_);});}else{if(!E(_8H[2])[0]){var _8I=B(A(_8y,[_8B,_8G[1],_])),_8J=B(A(_8y,[_8C,_8H[1],_]));return [0,_8I,_8J];}else{return new F(function(){return _8x(_);});}}}},_8K=function(_){return new F(function(){return __jsNull();});},_8L=function(_8M){var _8N=B(A(_8M,[_]));return E(_8N);},_8O=new T(function(){return B(_8L(_8K));}),_8P=new T(function(){return E(_8O);}),_8Q=function(_8R,_8S,_){if(E(_8R)==7){var _8T=E(_8b)(_8S),_8U=B(_8A(_8p,_8p,_8T,_)),_8V=_8S[E(_7N)],_8W=_8S[E(_7M)],_8X=_8S[E(_7L)];return new T(function(){return [0,E(_8U),E(_6t),[0,_8V,_8W,_8X]];});}else{var _8Y=E(_8b)(_8S),_8Z=B(_8A(_8p,_8p,_8Y,_)),_90=_8S[E(_8a)],_91=__eq(_90,E(_8P));if(!E(_91)){var _92=B(_84(_90,_));return new T(function(){return [0,E(_8Z),[1,_92],E(_89)];});}else{return new T(function(){return [0,E(_8Z),E(_6t),E(_89)];});}}},_93=function(_94,_95,_){return new F(function(){return _8Q(_94,E(_95),_);});},_96="mouseout",_97="mouseover",_98="mousemove",_99="mouseup",_9a="mousedown",_9b="dblclick",_9c="click",_9d="wheel",_9e=function(_9f){switch(E(_9f)){case 0:return E(_9c);case 1:return E(_9b);case 2:return E(_9a);case 3:return E(_99);case 4:return E(_98);case 5:return E(_97);case 6:return E(_96);default:return E(_9d);}},_9g=[0,_9e,_93],_9h=function(_){return new F(function(){return E(_4)("td");});},_9i=function(_9j){return E(E(_9j)[1]);},_9k=function(_9l){return E(E(_9l)[3]);},_9m=function(_9n){return E(E(_9n)[2]);},_9o=function(_9p){return E(E(_9p)[4]);},_9q=(function(c,p){p.appendChild(c);}),_9r=function(_9s){return E(E(_9s)[1]);},_9t=(function(e,p,v){e.setAttribute(p, v);}),_9u=(function(e,p,v){e.style[p] = v;}),_9v=function(_9w,_9x,_9y,_9z){var _9A=new T(function(){return B(A(_9r,[_9w,_9y]));}),_9B=function(_9C,_){var _9D=E(_9C);if(!_9D[0]){return _a;}else{var _9E=E(_9A),_9F=E(_9q),_9G=_9F(E(_9D[1]),_9E),_9H=_9D[2];while(1){var _9I=E(_9H);if(!_9I[0]){return _a;}else{var _9J=_9F(E(_9I[1]),_9E);_9H=_9I[2];continue;}}}},_9K=function(_9L,_){while(1){var _9M=B((function(_9N,_){var _9O=E(_9N);if(!_9O[0]){return _a;}else{var _9P=_9O[2],_9Q=E(_9O[1]);if(!_9Q[0]){var _9R=_9Q[2],_9S=E(_9Q[1]);switch(_9S[0]){case 0:var _9T=E(_9A),_9U=E(_1),_9V=_9U(_9T,_9S[1],_9R),_9W=_9P;while(1){var _9X=E(_9W);if(!_9X[0]){return _a;}else{var _9Y=_9X[2],_9Z=E(_9X[1]);if(!_9Z[0]){var _a0=_9Z[2],_a1=E(_9Z[1]);switch(_a1[0]){case 0:var _a2=_9U(_9T,_a1[1],_a0);_9W=_9Y;continue;case 1:var _a3=E(_9u)(_9T,_a1[1],_a0);_9W=_9Y;continue;default:var _a4=E(_9t)(_9T,_a1[1],_a0);_9W=_9Y;continue;}}else{var _a5=B(_9B(_9Z[1],_));_9W=_9Y;continue;}}}break;case 1:var _a6=E(_9A),_a7=E(_9u),_a8=_a7(_a6,_9S[1],_9R),_a9=_9P;while(1){var _aa=E(_a9);if(!_aa[0]){return _a;}else{var _ab=_aa[2],_ac=E(_aa[1]);if(!_ac[0]){var _ad=_ac[2],_ae=E(_ac[1]);switch(_ae[0]){case 0:var _af=E(_1)(_a6,_ae[1],_ad);_a9=_ab;continue;case 1:var _ag=_a7(_a6,_ae[1],_ad);_a9=_ab;continue;default:var _ah=E(_9t)(_a6,_ae[1],_ad);_a9=_ab;continue;}}else{var _ai=B(_9B(_ac[1],_));_a9=_ab;continue;}}}break;default:var _aj=E(_9A),_ak=E(_9t),_al=_ak(_aj,_9S[1],_9R),_am=_9P;while(1){var _an=E(_am);if(!_an[0]){return _a;}else{var _ao=_an[2],_ap=E(_an[1]);if(!_ap[0]){var _aq=_ap[2],_ar=E(_ap[1]);switch(_ar[0]){case 0:var _as=E(_1)(_aj,_ar[1],_aq);_am=_ao;continue;case 1:var _at=E(_9u)(_aj,_ar[1],_aq);_am=_ao;continue;default:var _au=_ak(_aj,_ar[1],_aq);_am=_ao;continue;}}else{var _av=B(_9B(_ap[1],_));_am=_ao;continue;}}}}}else{var _aw=B(_9B(_9Q[1],_));_9L=_9P;return null;}}})(_9L,_));if(_9M!=null){return _9M;}}};return new F(function(){return A(_2,[_9x,function(_){return new F(function(){return _9K(_9z,_);});}]);});},_ax=function(_ay,_az,_aA,_aB){var _aC=B(_9i(_az)),_aD=function(_aE){return new F(function(){return A(_9k,[_aC,new T(function(){return B(_9v(_ay,_az,_aE,_aB));}),new T(function(){return B(A(_9o,[_aC,_aE]));})]);});};return new F(function(){return A(_9m,[_aC,_aA,_aD]);});},_aF=function(_aG,_){var _aH=E(_aG);if(!_aH[0]){return _3n;}else{var _aI=B(A(_ax,[_S,_6B,_9h,[1,[1,[1,_aH[1],_3n]],_3n],_])),_aJ=B(_aF(_aH[2],_));return [1,_aI,_aJ];}},_aK=function(_aL,_aM,_){var _aN=B(A(_ax,[_S,_6B,_9h,[1,[1,[1,_aL,_3n]],_3n],_])),_aO=B(_aF(_aM,_));return [1,_aN,_aO];},_aP=(function(s){return document.createTextNode(s);}),_aQ=function(_aR,_){var _aS=jsShow(_aR),_aT=E(_aP)(toJSStr(fromJSStr(_aS)));return new F(function(){return A(_ax,[_S,_6B,_9h,[1,[1,[1,_aT,_3n]],_3n],_]);});},_aU=function(_aV,_aW){var _aX=(_aW-_aV)*25/900;if(!_aX){var _aY=rintDouble(0);return _aY&4294967295;}else{if(_aX<=0){var _aZ=rintDouble( -_aX/0.1);return _aZ&4294967295;}else{var _b0=rintDouble(_aX/0.1);return _b0&4294967295;}}},_b1=function(_b2,_b3){return [0,E(_b2),toJSStr(E(_b3))];},_b4=2,_b5=0,_b6=new T(function(){return B(unCStr("x1"));}),_b7=new T(function(){return B(unCStr("y1"));}),_b8=new T(function(){return B(unCStr("x2"));}),_b9=new T(function(){return B(unCStr("y2"));}),_ba=new T(function(){return B(unCStr("frames"));}),_bb=new T(function(){return B(unCStr("time (minutes)"));}),_bc=new T(function(){return B(unCStr("title"));}),_bd=new T(function(){return B(unCStr("Delete"));}),_be=[1,_bd,_3n],_bf=[1,_bc,_be],_bg=[1,_bb,_bf],_bh=[1,_ba,_bg],_bi=[1,_b9,_bh],_bj=[1,_b8,_bi],_bk=function(_){return new F(function(){return E(_4)("span");});},_bl=new T(function(){return [0,[2,"class"],"glyphicon glyphicon-remove"];}),_bm=[1,_bl,_3n],_bn=new T(function(){return B(_ax(_S,_6B,_bk,_bm));}),_bo=function(_){return new F(function(){return E(_4)("input");});},_bp=function(_){return new F(function(){return E(_4)("tr");});},_bq=function(_){return new F(function(){return E(_4)("th");});},_br=function(_){return new F(function(){return E(_4)("button");});},_bs=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_bt=function(_bu){var _bv=I_decodeDouble(_bu);return [0,[1,_bv[2]],_bv[1]];},_bw=function(_bx){var _by=E(_bx);if(!_by[0]){return _by[1];}else{return new F(function(){return I_toNumber(_by[1]);});}},_bz=function(_bA){return [0,_bA];},_bB=function(_bC){var _bD=hs_intToInt64(2147483647),_bE=hs_leInt64(_bC,_bD);if(!_bE){return [1,I_fromInt64(_bC)];}else{var _bF=hs_intToInt64(-2147483648),_bG=hs_geInt64(_bC,_bF);if(!_bG){return [1,I_fromInt64(_bC)];}else{var _bH=hs_int64ToInt(_bC);return new F(function(){return _bz(_bH);});}}},_bI=function(_bJ){var _bK=hs_intToInt64(_bJ);return E(_bK);},_bL=function(_bM){var _bN=E(_bM);if(!_bN[0]){return new F(function(){return _bI(_bN[1]);});}else{return new F(function(){return I_toInt64(_bN[1]);});}},_bO=new T(function(){return [2,"value"];}),_bP=new T(function(){return [0,[2,"type"],"text"];}),_bQ=new T(function(){return [0,[2,"class"],"btn btn-danger"];}),_bR=function(_bS){return E(E(_bS)[1]);},_bT=function(_bU){return E(E(_bU)[2]);},_bV=function(_bW){return E(E(_bW)[1]);},_bX=function(_){return new F(function(){return nMV(_6t);});},_bY=new T(function(){return B(_8L(_bX));}),_bZ=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_c0=function(_c1){return E(E(_c1)[2]);},_c2=function(_c3,_c4,_c5,_c6,_c7,_c8){var _c9=B(_bR(_c3)),_ca=B(_9i(_c9)),_cb=new T(function(){return B(_2(_c9));}),_cc=new T(function(){return B(_9o(_ca));}),_cd=new T(function(){return B(A(_9r,[_c4,_c6]));}),_ce=new T(function(){return B(A(_bV,[_c5,_c7]));}),_cf=function(_cg){return new F(function(){return A(_cc,[[0,_ce,_cd,_cg]]);});},_ch=function(_ci){var _cj=new T(function(){var _ck=new T(function(){var _cl=__createJSFunc(2,function(_cm,_){var _cn=B(A(E(_ci),[_cm,_]));return _8P;}),_co=_cl;return function(_){return new F(function(){return E(_bZ)(E(_cd),E(_ce),_co);});};});return B(A(_cb,[_ck]));});return new F(function(){return A(_9m,[_ca,_cj,_cf]);});},_cp=new T(function(){var _cq=new T(function(){return B(_2(_c9));}),_cr=function(_cs){var _ct=new T(function(){return B(A(_cq,[function(_){var _=wMV(E(_bY),[1,_cs]);return new F(function(){return A(_bT,[_c5,_c7,_cs,_]);});}]));});return new F(function(){return A(_9m,[_ca,_ct,_c8]);});};return B(A(_c0,[_c3,_cr]));});return new F(function(){return A(_9m,[_ca,_cp,_ch]);});},_cu=function(_cv,_cw){while(1){var _cx=E(_cv);if(!_cx[0]){return E(_cw);}else{var _cy=[1,_cx[1],_cw];_cv=_cx[2];_cw=_cy;continue;}}},_cz=function(_cA,_cB){while(1){var _cC=E(_cA);if(!_cC[0]){_cA=[1,I_fromInt(_cC[1])];continue;}else{return [1,I_shiftLeft(_cC[1],_cB)];}}},_cD=function(_cE,_cF,_cG,_cH,_){var _cI=E(_bs)(_cH),_cJ=E(_aP),_cK=_cJ(toJSStr(E(_b6))),_cL=B(A(_ax,[_S,_6B,_bq,[1,[1,[1,_cK,_3n]],_3n],_])),_cM=function(_cN,_){var _cO=E(_cN);if(!_cO[0]){return _3n;}else{var _cP=_cJ(toJSStr(E(_cO[1]))),_cQ=B(A(_ax,[_S,_6B,_bq,[1,[1,[1,_cP,_3n]],_3n],_])),_cR=B(_cM(_cO[2],_));return [1,_cQ,_cR];}},_cS=B((function(_cT,_cU,_){var _cV=_cJ(toJSStr(E(_cT))),_cW=B(A(_ax,[_S,_6B,_bq,[1,[1,[1,_cV,_3n]],_3n],_])),_cX=B(_cM(_cU,_));return [1,_cW,_cX];})(_b7,_bj,_)),_cY=B(A(_ax,[_S,_6B,_bp,[1,[1,[1,_cL,_cS]],_3n],_])),_cZ=E(_9q),_d0=_cZ(E(_cY),_cH),_d1=function(_d2,_){var _d3=E(_d2);if(!_d3[0]){return _3n;}else{var _d4=E(_d3[1]),_d5=E(_d4[1]),_d6=E(_d4[2]),_d7=E(_d5[1]),_d8=B(_aQ(_d7*25/900,_)),_d9=_d8,_da=E(_d5[2]),_db=B(_aQ(_da*25/900,_)),_dc=_db,_dd=E(_d6[1]),_de=B(_aQ(_dd*25/900,_)),_df=_de,_dg=E(_d6[2]),_dh=B(_aQ(_dg*25/900,_)),_di=_dh,_dj=function(_dk){var _dl=B(_aQ(_dk,_)),_dm=_dl,_dn=function(_do){var _dp=rintDouble(_do*5.8333333333333334e-2),_dq=B(_bt(_dp)),_dr=_dq[1],_ds=_dq[2],_dt=function(_du){var _dv=B(_aQ(_du,_)),_dw=B(_aK(_d9,[1,_dc,[1,_df,[1,_di,[1,_dm,[1,_dv,_3n]]]]],_)),_dx=B(A(_ax,[_S,_6B,_bp,[1,new T(function(){return B(_7J(_dw));}),_3n],_])),_dy=B(A(_ax,[_S,_6B,_bo,[1,_bP,[1,new T(function(){return B(_b1(_bO,_d4[3]));}),_3n]],_])),_dz=B(A(_bn,[_])),_dA=B(A(_ax,[_S,_6B,_br,[1,_bQ,[1,[1,[1,_dz,_3n]],_3n]],_])),_dB=B(A(_ax,[_S,_6B,_9h,[1,[1,[1,_dy,_3n]],_3n],_])),_dC=E(_dx),_dD=_cZ(E(_dB),_dC),_dE=E(_dA),_dF=_cZ(_dE,_dC),_dG=new T(function(){return B(A(_cF,[_d4]));}),_dH=B(A(_c2,[_6C,_S,_9g,_dE,_b5,function(_dI){return E(_dG);},_])),_dJ=new T(function(){return B(A(_cE,[_dy,_d4]));}),_dK=B(A(_c2,[_6C,_S,_o,_dy,_b4,function(_dL){return E(_dJ);},_])),_dM=_cZ(_dC,_cH),_dN=B(_d1(_d3[2],_));return [1,_a,_dN];};if(_ds>=0){return new F(function(){return _dt(B(_bw(B(_cz(_dr,_ds)))));});}else{var _dO=hs_uncheckedIShiftRA64(B(_bL(_dr)), -_ds);return new F(function(){return _dt(B(_bw(B(_bB(_dO)))));});}};if(_d7!=_dd){return new F(function(){return _dn(B(_aU(_d7,_dd)));});}else{return new F(function(){return _dn(B(_aU(_da,_dg)));});}};if(_d7!=_dd){return new F(function(){return _dj(B(_aU(_d7,_dd)));});}else{return new F(function(){return _dj(B(_aU(_da,_dg)));});}}},_dP=B(_d1(B(_cu(E(_cG)[2],_3n)),_));return _a;},_dQ=function(_){return _a;},_dR=(function(ctx){ctx.restore();}),_dS=(function(ctx){ctx.save();}),_dT=(function(ctx,x,y){ctx.scale(x,y);}),_dU=function(_dV,_dW,_dX,_dY,_){var _dZ=E(_dS)(_dY),_e0=E(_dT)(_dY,E(_dV),E(_dW)),_e1=B(A(_dX,[_dY,_])),_e2=E(_dR)(_dY);return new F(function(){return _dQ(_);});},_e3=(function(ctx){ctx.beginPath();}),_e4=(function(ctx){ctx.stroke();}),_e5=function(_e6,_e7,_){var _e8=E(_e3)(_e7),_e9=B(A(_e6,[_e7,_])),_ea=E(_e4)(_e7);return new F(function(){return _dQ(_);});},_eb=(function(ctx,i,x,y){ctx.drawImage(i,x,y);}),_ec=function(_ed,_ee,_ef,_eg,_){var _eh=E(_eb)(_eg,_ed,_ee,_ef);return new F(function(){return _dQ(_);});},_ei=",",_ej="[",_ek="]",_el="{",_em="}",_en=":",_eo="\"",_ep="true",_eq="false",_er="null",_es=new T(function(){return JSON.stringify;}),_et=function(_eu,_ev){var _ew=E(_ev);switch(_ew[0]){case 0:return [0,new T(function(){return jsShow(_ew[1]);}),_eu];case 1:return [0,new T(function(){var _ex=E(_es)(_ew[1]);return String(_ex);}),_eu];case 2:return (!E(_ew[1]))?[0,_eq,_eu]:[0,_ep,_eu];case 3:var _ey=E(_ew[1]);if(!_ey[0]){return [0,_ej,[1,_ek,_eu]];}else{var _ez=new T(function(){var _eA=new T(function(){var _eB=function(_eC){var _eD=E(_eC);if(!_eD[0]){return [1,_ek,_eu];}else{var _eE=new T(function(){var _eF=B(_et(new T(function(){return B(_eB(_eD[2]));}),_eD[1]));return [1,_eF[1],_eF[2]];});return [1,_ei,_eE];}};return B(_eB(_ey[2]));}),_eG=B(_et(_eA,_ey[1]));return [1,_eG[1],_eG[2]];});return [0,_ej,_ez];}break;case 4:var _eH=E(_ew[1]);if(!_eH[0]){return [0,_el,[1,_em,_eu]];}else{var _eI=E(_eH[1]),_eJ=new T(function(){var _eK=new T(function(){var _eL=function(_eM){var _eN=E(_eM);if(!_eN[0]){return [1,_em,_eu];}else{var _eO=E(_eN[1]),_eP=new T(function(){var _eQ=B(_et(new T(function(){return B(_eL(_eN[2]));}),_eO[2]));return [1,_eQ[1],_eQ[2]];});return [1,_ei,[1,_eo,[1,_eO[1],[1,_eo,[1,_en,_eP]]]]];}};return B(_eL(_eH[2]));}),_eR=B(_et(_eK,_eI[2]));return [1,_eR[1],_eR[2]];});return [0,_el,[1,new T(function(){var _eS=E(_es)(E(_eI[1]));return String(_eS);}),[1,_en,_eJ]]];}break;default:return [0,_er,_eu];}},_eT=new T(function(){return toJSStr(_3n);}),_eU=function(_eV){var _eW=B(_et(_3n,_eV)),_eX=jsCat([1,_eW[1],_eW[2]],E(_eT));return E(_eX);},_eY=function(_eZ,_f0){return E(_eZ)!=E(_f0);},_f1=function(_f2,_f3){return E(_f2)==E(_f3);},_f4=[0,_f1,_eY],_f5=function(_f6,_f7,_f8){while(1){var _f9=E(_f8);if(!_f9[0]){return false;}else{if(!B(A(_T,[_f6,_f7,_f9[1]]))){_f8=_f9[2];continue;}else{return true;}}}},_fa=32,_fb=function(_fc){while(1){var _fd=E(_fc);if(!_fd[0]){return false;}else{var _fe=E(_fd[1]);if(!_fe[0]){return true;}else{if(!B(_f5(_f4,_fa,_fe))){_fc=_fd[2];continue;}else{return true;}}}}},_ff=function(_fg){return E(E(_fg)[3]);},_fh=function(_fi,_fj,_fk){var _fl=E(_fi);return (_fl[0]==0)?false:(!B(_fb(B(_1A(_ff,_fl)))))?(!B(_26(_fj,_3n)))?(!B(_f5(_f4,_fa,_fj)))?(E(_fk)[0]==0)?false:true:false:false:false;},_fm=function(_fn){while(1){var _fo=E(_fn);if(!_fo[0]){_fn=[1,I_fromInt(_fo[1])];continue;}else{return new F(function(){return I_toString(_fo[1]);});}}},_fp=function(_fq,_fr){return new F(function(){return _16(fromJSStr(B(_fm(_fq))),_fr);});},_fs=function(_ft,_fu){var _fv=E(_ft);if(!_fv[0]){var _fw=_fv[1],_fx=E(_fu);return (_fx[0]==0)?_fw<_fx[1]:I_compareInt(_fx[1],_fw)>0;}else{var _fy=_fv[1],_fz=E(_fu);return (_fz[0]==0)?I_compareInt(_fy,_fz[1])<0:I_compare(_fy,_fz[1])<0;}},_fA=[0,0],_fB=function(_fC,_fD,_fE){if(_fC<=6){return new F(function(){return _fp(_fD,_fE);});}else{if(!B(_fs(_fD,_fA))){return new F(function(){return _fp(_fD,_fE);});}else{return [1,_7T,new T(function(){return B(_16(fromJSStr(B(_fm(_fD))),[1,_7S,_fE]));})];}}},_fF=0,_fG=1,_fH=function(_fI){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_fI));}))));});},_fJ=new T(function(){return B(_fH("ww_sphV MouseState"));}),_fK=new T(function(){return B(_fH("ww_sphX String"));}),_fL=function(_fM){var _fN=E(_fM);if(!_fN[0]){return [0];}else{return new F(function(){return _16(_fN[1],new T(function(){return B(_fL(_fN[2]));},1));});}},_fO=new T(function(){return B(unCStr("\r\n"));}),_fP=new T(function(){return B(_16(_fO,_fO));}),_fQ=function(_fR,_fS){var _fT=E(_fS);return (_fT[0]==0)?[0]:[1,_fR,[1,_fT[1],new T(function(){return B(_fQ(_fR,_fT[2]));})]];},_fU=new T(function(){return B(unCStr("  ccdacq"));}),_fV=new T(function(){return B(unAppCStr("}",_fO));}),_fW=new T(function(){return B(_16(_fO,_fV));}),_fX=new T(function(){return B(_7U(0,1,_3n));}),_fY=new T(function(){return B(unCStr("1"));}),_fZ=new T(function(){return B(_16(_fY,_3n));}),_g0=[1,_fa,_fZ],_g1=new T(function(){return B(_16(_fX,_g0));}),_g2=[1,_fa,_g1],_g3=new T(function(){var _g4=jsShow(0);return fromJSStr(_g4);}),_g5=new T(function(){var _g6=jsShow(0.1);return fromJSStr(_g6);}),_g7=new T(function(){return B(unCStr("ccdtrans sav"));}),_g8=function(_g9,_ga,_gb,_gc){if(!E(_g9)){var _gd=new T(function(){var _ge=E(_gb),_gf=E(_ge[1]),_gg=_gf[2],_gh=E(_ga),_gi=function(_gj){var _gk=jsShow(_gj),_gl=new T(function(){var _gm=new T(function(){var _gn=new T(function(){var _go=E(_gf[1]),_gp=E(_ge[2]),_gq=E(_gp[1]),_gr=function(_gs){var _gt=new T(function(){var _gu=new T(function(){var _gv=new T(function(){var _gw=new T(function(){var _gx=new T(function(){var _gy=new T(function(){var _gz=E(_gh[6]),_gA=E(_gc),_gB=_gz+12.5+(_go*25/900-12.5)*Math.cos(_gA),_gC=jsShow(_gB),_gD=new T(function(){var _gE=new T(function(){var _gF=jsShow((_gz+12.5+(_gq*25/900-12.5)*Math.cos(_gA)-_gB)/_gs),_gG=new T(function(){var _gH=new T(function(){var _gI=new T(function(){var _gJ=(_go*25/900-12.5)*Math.sin(_gA),_gK=jsShow(_gJ),_gL=new T(function(){var _gM=new T(function(){var _gN=jsShow(((_gq*25/900-12.5)*Math.sin(_gA)-_gJ)/_gs),_gO=new T(function(){var _gP=new T(function(){var _gQ=new T(function(){var _gR=new T(function(){var _gS=new T(function(){var _gT=new T(function(){var _gU=new T(function(){return B(_16(_g5,[1,_fa,new T(function(){return B(_16(_ge[3],_3n));})]));});return B(_16(B(_16(_fU,[1,_fa,_gU])),_fW));},1);return B(_16(_fO,_gT));});return B(unAppCStr("  umv tmp2 x",_gS));},1);return B(_16(_fO,_gR));});return B(unAppCStr("  umv sah y",_gQ));},1);return B(_16(_fO,_gP));},1);return B(_16(fromJSStr(_gN),_gO));});return B(unAppCStr("+i*",_gM));},1);return B(_16(fromJSStr(_gK),_gL));});return B(unAppCStr("  x = ",_gI));},1);return B(_16(_fO,_gH));},1);return B(_16(fromJSStr(_gF),_gG));});return B(unAppCStr("+i*",_gE));},1);return B(_16(fromJSStr(_gC),_gD));});return B(unAppCStr("  y = ",_gy));},1);return B(_16(_fO,_gx));});return B(unAppCStr("{",_gw));},1);return B(_16(_fO,_gv));});return B(unAppCStr(";i+=1)",_gu));},1);return new F(function(){return _16(B(_7U(0,_gs,_3n)),_gt);});};if(_go!=_gq){return B(_gr(B(_aU(_go,_gq))));}else{return B(_gr(B(_aU(E(_gg),E(_gp[2])))));}});return B(unAppCStr("for(i=0;i<=",_gn));},1);return B(_16(_fO,_gm));},1);return new F(function(){return _16(fromJSStr(_gk),_gl);});};if(!E(_gh[7])){return B(_gi(E(_gh[4])+E(_gg)*25/900));}else{return B(_gi(E(_gh[5])+E(_gg)*25/900));}});return new F(function(){return unAppCStr("umv sav ",_gd);});}else{var _gV=new T(function(){var _gW=E(_gb),_gX=E(_gW[1]),_gY=_gX[2],_gZ=E(_ga),_h0=_gZ[4],_h1=_gZ[5],_h2=_gZ[7],_h3=E(_gX[1]),_h4=E(_gc),_h5=jsShow(E(_gZ[6])+12.5+(_h3*25/900-12.5)*Math.cos(_h4)),_h6=new T(function(){var _h7=new T(function(){var _h8=jsShow((_h3*25/900-12.5)*Math.sin(_h4)),_h9=new T(function(){var _ha=new T(function(){var _hb=new T(function(){var _hc=new T(function(){var _hd=E(_gW[2]),_he=_hd[2],_hf=new T(function(){var _hg=new T(function(){var _hh=E(_hd[1]),_hi=function(_hj){var _hk=new T(function(){return B(_16(_g3,[1,_fa,new T(function(){return B(_16(_gW[3],_g2));})]));});return new F(function(){return _16(B(_7U(0,_hj,_3n)),[1,_fa,_hk]);});};if(_h3!=_hh){return B(_hi(B(_aU(_h3,_hh))));}else{return B(_hi(B(_aU(E(_gY),E(_he)))));}});return B(_16(_g5,[1,_fa,_hg]));});if(!E(_h2)){var _hl=jsShow(E(_h0)+E(_he)*25/900);return B(_16(fromJSStr(_hl),[1,_fa,_hf]));}else{var _hm=jsShow(E(_h1)+E(_he)*25/900);return B(_16(fromJSStr(_hm),[1,_fa,_hf]));}});if(!E(_h2)){var _hn=jsShow(E(_h0)+E(_gY)*25/900);return B(_16(fromJSStr(_hn),[1,_fa,_hc]));}else{var _ho=jsShow(E(_h1)+E(_gY)*25/900);return B(_16(fromJSStr(_ho),[1,_fa,_hc]));}});return B(_16(_g7,[1,_fa,_hb]));},1);return B(_16(_fO,_ha));},1);return B(_16(fromJSStr(_h8),_h9));});return B(unAppCStr(" tmp2 ",_h7));},1);return B(_16(fromJSStr(_h5),_h6));});return new F(function(){return unAppCStr("umv sah ",_gV);});}},_hp=function(_hq,_hr,_hs,_ht,_hu,_hv){var _hw=[0,_fJ,_hq,_fK,_hr,_hs,_ht,_hu,_hv],_hx=function(_hy){var _hz=new T(function(){var _hA=E(_hy),_hB=rintDouble(_hA*180/3.141592653589793),_hC=B(_bt(_hB)),_hD=_hC[1],_hE=_hC[2],_hF=new T(function(){var _hG=new T(function(){var _hH=B(_1A(function(_hI){var _hJ=E(_hI);if(E(E(_hJ[1])[1])!=E(E(_hJ[2])[1])){return new F(function(){return _g8(_fF,_hw,_hJ,_hA);});}else{return new F(function(){return _g8(_fG,_hw,_hJ,_hA);});}},B(_cu(_hq,_3n))));if(!_hH[0]){return [0];}else{return B(_fL([1,_hH[1],new T(function(){return B(_fQ(_fO,_hH[2]));})]));}},1);return B(_16(_fO,_hG));});if(_hE>=0){return B(_16(B(_fB(0,B(_cz(_hD,_hE)),_3n)),_hF));}else{var _hK=hs_uncheckedIShiftRA64(B(_bL(_hD)), -_hE);return B(_16(B(_fB(0,B(_bB(_hK)),_3n)),_hF));}});return new F(function(){return unAppCStr("umv sar ",_hz);});},_hL=B(_1A(_hx,_hv));if(!_hL[0]){return [0];}else{return new F(function(){return _fL([1,_hL[1],new T(function(){return B(_fQ(_fP,_hL[2]));})]);});}},_hM=(function(id){return document.getElementById(id);}),_hN=function(_hO,_hP){var _hQ=function(_){var _hR=E(_hM)(E(_hP)),_hS=__eq(_hR,E(_8P));return (E(_hS)==0)?[1,_hR]:_6t;};return new F(function(){return A(_2,[_hO,_hQ]);});},_hT=new T(function(){return encodeURIComponent;}),_hU=new T(function(){return B(unCStr("data:text/plain;charset=utf-8,"));}),_hV=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:190:3-9"));}),_hW=[0,_6t,_6u,_3n,_hV,_6t,_6t],_hX=new T(function(){return B(_6r(_hW));}),_hY=new T(function(){return B(unCStr("href"));}),_hZ=function(_i0){return new F(function(){return toJSStr(E(_i0));});},_i1=function(_i2,_i3,_){var _i4=B(A(_hN,[_6B,new T(function(){return B(_hZ(_i2));},1),_])),_i5=E(_i4);if(!_i5[0]){return new F(function(){return die(_hX);});}else{var _i6=E(_hT)(toJSStr(_i3)),_i7=E(_9t)(E(_i5[1]),toJSStr(E(_hY)),toJSStr(B(_16(_hU,new T(function(){var _i8=String(_i6);return fromJSStr(_i8);},1)))));return new F(function(){return _dQ(_);});}},_i9=(function(ctx,rad){ctx.rotate(rad);}),_ia=function(_ib,_ic,_id,_){var _ie=E(_dS)(_id),_if=E(_i9)(_id,E(_ib)),_ig=B(A(_ic,[_id,_])),_ih=E(_dR)(_id);return new F(function(){return _dQ(_);});},_ii=(function(ctx,x,y){ctx.translate(x,y);}),_ij=function(_ik,_il,_im,_in,_){var _io=E(_dS)(_in),_ip=E(_ii)(_in,E(_ik),E(_il)),_iq=B(A(_im,[_in,_])),_ir=E(_dR)(_in);return new F(function(){return _dQ(_);});},_is=function(_it,_iu){if(_iu<=0){var _iv=function(_iw){var _ix=function(_iy){var _iz=function(_iA){var _iB=function(_iC){var _iD=isDoubleNegativeZero(_iu),_iE=_iD,_iF=function(_iG){var _iH=E(_it);if(!_iH){return (_iu>=0)?(E(_iE)==0)?E(_iu):3.141592653589793:3.141592653589793;}else{var _iI=E(_iu);return (_iI==0)?E(_iH):_iI+_iH;}};if(!E(_iE)){return new F(function(){return _iF(_);});}else{var _iJ=E(_it),_iK=isDoubleNegativeZero(_iJ);if(!E(_iK)){return new F(function(){return _iF(_);});}else{return  -B(_is( -_iJ,_iu));}}};if(_iu>=0){return new F(function(){return _iB(_);});}else{var _iL=E(_it),_iM=isDoubleNegativeZero(_iL);if(!E(_iM)){return new F(function(){return _iB(_);});}else{return  -B(_is( -_iL,_iu));}}};if(_iu>0){return new F(function(){return _iz(_);});}else{var _iN=E(_it);if(_iN>=0){return new F(function(){return _iz(_);});}else{return  -B(_is( -_iN,_iu));}}};if(_iu>=0){return new F(function(){return _ix(_);});}else{var _iO=E(_it);if(_iO<=0){return new F(function(){return _ix(_);});}else{return 3.141592653589793+Math.atan(_iO/_iu);}}};if(!E(_iu)){if(E(_it)<=0){return new F(function(){return _iv(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _iv(_);});}}else{return new F(function(){return Math.atan(E(_it)/_iu);});}},_iP=function(_iQ,_iR){return E(_iQ)-E(_iR);},_iS=function(_iT,_iU,_iV,_iW,_iX,_iY,_iZ,_j0){return new F(function(){return Math.atan((Math.tan(B(_is(new T(function(){return B(_iP(_iW,_iU));}),_iV-_iT))-1.5707963267948966)+Math.tan(B(_is(new T(function(){return B(_iP(_iY,_iW));}),_iX-_iV)))+Math.tan(B(_is(new T(function(){return B(_iP(_j0,_iY));}),_iZ-_iX))+1.5707963267948966)+Math.tan(B(_is(new T(function(){return B(_iP(_iU,_j0));}),_iT-_iZ))-3.141592653589793))/4);});},_j1=function(_j2){return E(_j2)/2;},_j3=function(_j4,_j5,_j6,_){var _j7=E(_j4);return new F(function(){return _ij(_j7[1],_j7[2],_j5,E(_j6),_);});},_j8=function(_j9,_ja){var _jb=new T(function(){var _jc=E(_j9),_jd=E(E(_ja)[2]),_je=E(_jd[1]),_jf=E(_je[1]),_jg=E(_je[2]),_jh=E(_jd[2]),_ji=E(_jh[1]),_jj=E(_jh[2]),_jk=E(_jd[3]),_jl=E(_jk[1]),_jm=E(_jk[2]),_jn=E(_jd[4]),_jo=E(_jn[1]),_jp=E(_jn[2]);return Math.sqrt(E(_jc[1])*E(_jc[2])/(0.5*(_jf*_jp+_jo*_jm+_jl*_jg-_jf*_jm-_jl*_jp-_jo*_jg)+0.5*(_jo*_jm+_jl*_jj+_ji*_jp-_jo*_jj-_ji*_jm-_jl*_jp)));}),_jq=new T(function(){var _jr=E(_j9);return [0,new T(function(){return B(_j1(_jr[1]));}),new T(function(){return B(_j1(_jr[2]));})];}),_js=new T(function(){var _jt=E(E(_ja)[2]),_ju=E(_jt[1]),_jv=E(_jt[2]),_jw=E(_jt[3]),_jx=E(_jt[4]);return  -B(_iS(E(_ju[1]),_ju[2],E(_jv[1]),_jv[2],E(_jw[1]),_jw[2],E(_jx[1]),_jx[2]));}),_jy=new T(function(){var _jz=E(E(_ja)[2]),_jA=E(_jz[1]),_jB=E(_jz[2]),_jC=E(_jz[3]),_jD=E(_jz[4]);return [0,new T(function(){return (E(_jA[1])+E(_jB[1])+E(_jC[1])+E(_jD[1]))/4/(-1);}),new T(function(){return (E(_jA[2])+E(_jB[2])+E(_jC[2])+E(_jD[2]))/4/(-1);})];}),_jE=function(_jF,_jG,_){var _jH=E(_jq),_jI=function(_jJ,_){var _jK=function(_jL,_){return new F(function(){return _ia(_js,function(_jM,_){return new F(function(){return _j3(_jy,_jF,_jM,_);});},E(_jL),_);});};return new F(function(){return _dU(_jb,_jb,_jK,E(_jJ),_);});};return new F(function(){return _ij(_jH[1],_jH[2],_jI,E(_jG),_);});};return E(_jE);},_jN=(function(ctx,x,y){ctx.moveTo(x,y);}),_jO=(function(ctx,x,y){ctx.lineTo(x,y);}),_jP=function(_jQ,_jR,_){var _jS=E(_jQ);if(!_jS[0]){return _a;}else{var _jT=E(_jS[1]),_jU=E(_jR),_jV=E(_jN)(_jU,E(_jT[1]),E(_jT[2])),_jW=E(_jS[2]);if(!_jW[0]){return _a;}else{var _jX=E(_jW[1]),_jY=E(_jO),_jZ=_jY(_jU,E(_jX[1]),E(_jX[2])),_k0=_jW[2];while(1){var _k1=E(_k0);if(!_k1[0]){return _a;}else{var _k2=E(_k1[1]),_k3=_jY(_jU,E(_k2[1]),E(_k2[2]));_k0=_k1[2];continue;}}}}},_k4=function(_k5,_k6,_){var _k7=new T(function(){return E(E(_k5)[2]);}),_k8=new T(function(){return E(E(_k7)[1]);});return new F(function(){return _jP([1,_k8,[1,new T(function(){return E(E(_k7)[2]);}),[1,new T(function(){return E(E(_k7)[3]);}),[1,new T(function(){return E(E(_k7)[4]);}),[1,_k8,_3n]]]]],_k6,_);});},_k9=(function(e){e.width = e.width;}),_ka=",",_kb="rgba(",_kc=new T(function(){return toJSStr(_3n);}),_kd="rgb(",_ke=")",_kf=[1,_ke,_3n],_kg=function(_kh){var _ki=E(_kh);if(!_ki[0]){var _kj=jsCat([1,_kd,[1,new T(function(){return String(_ki[1]);}),[1,_ka,[1,new T(function(){return String(_ki[2]);}),[1,_ka,[1,new T(function(){return String(_ki[3]);}),_kf]]]]]],E(_kc));return E(_kj);}else{var _kk=jsCat([1,_kb,[1,new T(function(){return String(_ki[1]);}),[1,_ka,[1,new T(function(){return String(_ki[2]);}),[1,_ka,[1,new T(function(){return String(_ki[3]);}),[1,_ka,[1,new T(function(){return String(_ki[4]);}),_kf]]]]]]]],E(_kc));return E(_kk);}},_kl="strokeStyle",_km="fillStyle",_kn=(function(e,p){return e[p].toString();}),_ko=function(_kp,_kq){var _kr=new T(function(){return B(_kg(_kp));});return function(_ks,_){var _kt=E(_ks),_ku=E(_km),_kv=E(_kn),_kw=_kv(_kt,_ku),_kx=E(_kl),_ky=_kv(_kt,_kx),_kz=E(_kr),_kA=E(_1),_kB=_kA(_kt,_ku,_kz),_kC=_kA(_kt,_kx,_kz),_kD=B(A(_kq,[_kt,_])),_kE=String(_kw),_kF=_kA(_kt,_ku,_kE),_kG=String(_ky),_kH=_kA(_kt,_kx,_kG);return new F(function(){return _dQ(_);});};},_kI=function(_kJ,_kK,_kL){var _kM=E(_kL);if(!_kM[0]){return [0];}else{var _kN=_kM[1],_kO=_kM[2];return (!B(A(_kJ,[_kK,_kN])))?[1,_kN,new T(function(){return B(_kI(_kJ,_kK,_kO));})]:E(_kO);}},_kP="lineWidth",_kQ=function(_kR,_kS){var _kT=new T(function(){return String(E(_kR));});return function(_kU,_){var _kV=E(_kU),_kW=E(_kP),_kX=E(_kn)(_kV,_kW),_kY=E(_1),_kZ=_kY(_kV,_kW,E(_kT)),_l0=B(A(_kS,[_kV,_])),_l1=String(_kX),_l2=_kY(_kV,_kW,_l1);return new F(function(){return _dQ(_);});};},_l3=new T(function(){return B(unCStr("saveLink"));}),_l4=new T(function(){return B(unCStr("exportLink"));}),_l5=[0,255,0,255],_l6=1,_l7=0.2,_l8=900,_l9=[0,_l8,_l8],_la=new T(function(){return B(unCStr("btn btn-primary"));}),_lb=new T(function(){return B(unCStr("class"));}),_lc=new T(function(){return B(unCStr("btn btn-primary disabled"));}),_ld="exportLink",_le=new T(function(){return B(_hN(_6B,_ld));}),_lf=new T(function(){return B(unCStr("value"));}),_lg="runfile",_lh=new T(function(){return B(_hN(_6B,_lg));}),_li="scans",_lj=new T(function(){return B(_hN(_6B,_li));}),_lk=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:168:3-8"));}),_ll=[0,_6t,_6u,_3n,_lk,_6t,_6t],_lm=new T(function(){return B(_6r(_ll));}),_ln=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:150:3-14"));}),_lo=[0,_6t,_6u,_3n,_ln,_6t,_6t],_lp=new T(function(){return B(_6r(_lo));}),_lq=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:149:3-10"));}),_lr=[0,_6t,_6u,_3n,_lq,_6t,_6t],_ls=new T(function(){return B(_6r(_lr));}),_lt=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:148:3-11"));}),_lu=[0,_6t,_6u,_3n,_lt,_6t,_6t],_lv=new T(function(){return B(_6r(_lu));}),_lw="aligned",_lx=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:147:3-11"));}),_ly=[0,_6t,_6u,_3n,_lx,_6t,_6t],_lz=new T(function(){return B(_6r(_ly));}),_lA="original",_lB=function(_lC,_lD,_){while(1){var _lE=E(_lC);if(!_lE[0]){return _a;}else{var _lF=E(_lE[1]),_lG=B(_jP([1,_lF[1],[1,_lF[2],_3n]],_lD,_));_lC=_lE[2];continue;}}},_lH=[0,255,0,255],_lI=1,_lJ=function(_lK){var _lL=new T(function(){var _lM=function(_lN,_lO){return new F(function(){return _lB(E(_lK)[2],_lN,_lO);});};return B(_ko(_lH,function(_lP,_){return new F(function(){return _e5(_lM,E(_lP),_);});}));});return new F(function(){return _kQ(_lI,_lL);});},_lQ=function(_lR){return new F(function(){return fromJSStr(E(_lR));});},_lS=function(_lT,_lU,_lV,_lW){var _lX=new T(function(){var _lY=function(_){var _lZ=E(_kn)(B(A(_9r,[_lT,_lV])),E(_lW));return new T(function(){return String(_lZ);});};return E(_lY);});return new F(function(){return A(_2,[_lU,_lX]);});},_m0=function(_m1,_m2,_m3,_m4){var _m5=B(_9i(_m2)),_m6=new T(function(){return B(_9o(_m5));}),_m7=function(_m8){return new F(function(){return A(_m6,[new T(function(){return B(_lQ(_m8));})]);});},_m9=new T(function(){return B(_lS(_m1,_m2,_m3,new T(function(){return toJSStr(E(_m4));},1)));});return new F(function(){return A(_9m,[_m5,_m9,_m7]);});},_ma=new T(function(){return B(unCStr("value"));}),_mb=function(_mc,_md,_me){var _mf=E(_me);if(!_mf[0]){return [0];}else{var _mg=_mf[1],_mh=_mf[2];return (!B(A(_mc,[_mg])))?[1,_mg,new T(function(){return B(_mb(_mc,_md,_mh));})]:[1,new T(function(){return B(A(_md,[_mg]));}),new T(function(){return B(_mb(_mc,_md,_mh));})];}},_mi=function(_mj,_mk,_ml,_mm,_){var _mn=B(A(_m0,[_S,_6B,_ml,_ma,_])),_mo=_mn,_mp=E(_mk),_mq=rMV(_mp),_mr=E(_mq),_ms=new T(function(){return B(_mb(function(_mt){return new F(function(){return _6O(_mt,_mm);});},function(_mu){var _mv=E(_mu);return [0,_mv[1],_mv[2],_mo];},_mr[2]));}),_=wMV(_mp,[0,_mr[1],_ms,_mr[3],_mr[4],_mr[5],_mr[6],_mr[7],_mr[8]]);return new F(function(){return A(_mj,[_]);});},_mw=function(_mx,_my,_mz,_){var _mA=rMV(_my),_mB=_mA,_mC=E(_mx),_mD=rMV(_mC),_mE=_mD,_mF=B(A(_hN,[_6B,_lA,_])),_mG=E(_mF);if(!_mG[0]){return new F(function(){return die(_lz);});}else{var _mH=E(_mG[1]),_mI=E(_N),_mJ=_mI(_mH);if(!_mJ){return new F(function(){return die(_lz);});}else{var _mK=E(_M),_mL=_mK(_mH),_mM=_mL,_mN=B(A(_hN,[_6B,_lw,_])),_mO=function(_,_mP){var _mQ=E(_mP);if(!_mQ[0]){return new F(function(){return die(_lv);});}else{var _mR=B(A(_lj,[_])),_mS=E(_mR);if(!_mS[0]){return new F(function(){return die(_ls);});}else{var _mT=B(A(_lh,[_])),_mU=E(_mT);if(!_mU[0]){return new F(function(){return die(_lp);});}else{var _mV=E(_mE),_mW=_mV[2],_mX=_mV[8],_mY=E(_mV[3]),_mZ=E(_1)(E(_mU[1]),toJSStr(E(_lf)),toJSStr(_mY)),_n0=B(A(_le,[_])),_n1=E(_n0);if(!_n1[0]){return new F(function(){return die(_lm);});}else{var _n2=_n1[1],_n3=function(_){var _n4=function(_n5,_){var _n6=rMV(_mC),_n7=E(_n6),_=wMV(_mC,[0,_n7[1],new T(function(){return B(_kI(_6O,_n5,_n7[2]));}),_n7[3],_n7[4],_n7[5],_n7[6],_n7[7],_n7[8]]);return new F(function(){return _mw(_mC,_my,_mz,_);});},_n8=function(_){return new F(function(){return _mw(_mC,_my,_mz,_);});},_n9=B(_cD(function(_na,_nb,_){return new F(function(){return _mi(_n8,_mC,_na,_nb,_);});},_n4,_mV,E(_mS[1]),_)),_nc=E(_mz),_nd=rMV(_nc),_ne=_nd,_nf=E(_mQ[1]),_ng=_nf[1],_nh=E(_k9),_ni=_nh(_nf[2]),_nj=function(_nk,_){return new F(function(){return _ec(E(_ne),0,0,E(_nk),_);});},_nl=B(A(_j8,[_l9,_mB,function(_nm,_){return new F(function(){return _dU(_l7,_l7,_nj,E(_nm),_);});},_ng,_])),_nn=B(A(_lJ,[_mV,_ng,_])),_no=rMV(_nc),_np=_no,_nq=_nh(_mH),_nr=B(_dU(_l7,_l7,function(_ns,_){return new F(function(){return _ec(E(_np),0,0,E(_ns),_);});},_mM,_)),_nt=new T(function(){var _nu=function(_nb,_){return new F(function(){return _k4(_mB,_nb,_);});};return B(_ko(_l5,function(_nv,_){return new F(function(){return _e5(_nu,E(_nv),_);});}));}),_nw=B(A(_kQ,[_l6,_nt,_mM,_])),_nx=B(_i1(_l4,new T(function(){return B(_hp(_mW,_mV[4],_mV[5],_mV[6],_mV[7],_mX));},1),_)),_ny=new T(function(){return fromJSStr(B(_eU([4,E(B(_7C(_6Y,[1,new T(function(){return [4,E(B(_7g(_mB)))];}),[1,new T(function(){return [4,E(B(_7H(_mV)))];}),_3n]])))])));},1);return new F(function(){return _i1(_l3,_ny,_);});};if(!B(_fh(_mW,_mY,_mX))){var _nz=E(_9t)(E(_n2),toJSStr(E(_lb)),toJSStr(E(_lc)));return new F(function(){return _n3(_);});}else{var _nA=E(_9t)(E(_n2),toJSStr(E(_lb)),toJSStr(E(_la)));return new F(function(){return _n3(_);});}}}}}},_nB=E(_mN);if(!_nB[0]){return new F(function(){return _mO(_,_6t);});}else{var _nC=E(_nB[1]),_nD=_mI(_nC);if(!_nD){return new F(function(){return _mO(_,_6t);});}else{var _nE=_mK(_nC);return new F(function(){return _mO(_,[1,[0,_nE,_nC]]);});}}}}},_nF=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:101:3-9"));}),_nG=[0,_6t,_6u,_3n,_nF,_6t,_6t],_nH=new T(function(){return B(_6r(_nG));}),_nI=function(_){return new F(function(){return die(_nH);});},_nJ=2,_nK=function(_nL){return E(_nL)[2];},_nM=function(_){return _6t;},_nN=function(_nO,_){return new F(function(){return _nM(_);});},_nP=[0,_nK,_nN],_nQ=function(_nR,_nS){while(1){var _nT=E(_nR);if(!_nT[0]){return E(_nS);}else{var _nU=_nT[2],_nV=E(_nT[1]);if(_nS>_nV){_nR=_nU;_nS=_nV;continue;}else{_nR=_nU;continue;}}}},_nW=function(_nX,_nY,_nZ){var _o0=E(_nX);if(_nZ>_o0){return new F(function(){return _nQ(_nY,_o0);});}else{return new F(function(){return _nQ(_nY,_nZ);});}},_o1=2,_o2=4,_o3=3,_o4=function(_o5,_o6){var _o7=function(_o8,_o9){while(1){var _oa=B((function(_ob,_oc){var _od=E(_ob);if(!_od[0]){return [0];}else{var _oe=_od[2];if(!B(A(_o5,[_od[1]]))){var _of=_oc+1|0;_o8=_oe;_o9=_of;return null;}else{return [1,_oc,new T(function(){return B(_o7(_oe,_oc+1|0));})];}}})(_o8,_o9));if(_oa!=null){return _oa;}}},_og=B(_o7(_o6,0));return (_og[0]==0)?[0]:[1,_og[1]];},_oh=function(_oi){return E(_oi);},_oj=function(_ok,_ol,_om,_){var _on=function(_oo,_){var _op=E(_ok),_oq=rMV(_op),_or=E(E(_oq)[2]),_os=new T(function(){var _ot=new T(function(){var _ou=E(E(_oo)[1]);return [0,new T(function(){return B(_oh(_ou[1]));}),new T(function(){return B(_oh(_ou[2]));})];}),_ov=new T(function(){var _ow=E(_ot),_ox=E(_or[1]);return Math.pow(E(_ow[1])-E(_ox[1]),2)+Math.pow(E(_ow[2])-E(_ox[2]),2);}),_oy=new T(function(){var _oz=E(_ot),_oA=E(_or[2]);return Math.pow(E(_oz[1])-E(_oA[1]),2)+Math.pow(E(_oz[2])-E(_oA[2]),2);}),_oB=[1,new T(function(){var _oC=E(_ot),_oD=E(_or[3]);return Math.pow(E(_oC[1])-E(_oD[1]),2)+Math.pow(E(_oC[2])-E(_oD[2]),2);}),[1,new T(function(){var _oE=E(_ot),_oF=E(_or[4]);return Math.pow(E(_oE[1])-E(_oF[1]),2)+Math.pow(E(_oE[2])-E(_oF[2]),2);}),_3n]],_oG=new T(function(){return B(_nW(_oy,_oB,E(_ov)));}),_oH=B(_o4(function(_oI){return E(_oG)==E(_oI);},[1,_ov,[1,_oy,_oB]]));if(!_oH[0]){return 3;}else{switch(E(_oH[1])){case 0:return 0;break;case 1:return 2;break;case 3:return 1;break;default:return 3;}}}),_=wMV(_op,[0,[1,_os],_or]);return new F(function(){return A(_om,[_]);});},_oJ=B(A(_c2,[_6C,_nP,_9g,_ol,_o1,_on,_])),_oK=B(A(_c2,[_6C,_nP,_9g,_ol,_o3,function(_oL,_){var _oM=E(_ok),_oN=rMV(_oM),_=wMV(_oM,[0,_1Q,E(_oN)[2]]);return new F(function(){return A(_om,[_]);});},_])),_oO=function(_oP,_){var _oQ=E(_ok),_oR=rMV(_oQ),_oS=E(_oR),_oT=_oS[2],_oU=E(_oS[1]);if(!_oU[0]){var _oV=E(_oS);}else{var _oW=new T(function(){var _oX=E(E(_oP)[1]);return [0,new T(function(){return B(_oh(_oX[1]));}),new T(function(){return B(_oh(_oX[2]));})];});switch(E(_oU[1])){case 0:var _oY=E(_oT),_oZ=[0,_oU,[0,_oW,_oY[2],_oY[3],_oY[4]]];break;case 1:var _p0=E(_oT),_oZ=[0,_oU,[0,_p0[1],_p0[2],_p0[3],_oW]];break;case 2:var _p1=E(_oT),_oZ=[0,_oU,[0,_p1[1],_oW,_p1[3],_p1[4]]];break;default:var _p2=E(_oT),_oZ=[0,_oU,[0,_p2[1],_p2[2],_oW,_p2[4]]];}var _oV=_oZ;}var _=wMV(_oQ,_oV);return new F(function(){return A(_om,[_]);});},_p3=B(A(_c2,[_6C,_nP,_9g,_ol,_o2,_oO,_]));return _a;},_p4=function(_p5,_p6,_p7,_p8,_p9,_pa,_pb,_pc,_pd){if(!E(_p6)){return [0,_2W,_p7,_p8,_p9,_pa,_pb,_pc,_pd];}else{var _pe=E(_p7);if(!_pe[0]){return [0,_2U,_3n,_p8,_p9,_pa,_pb,_pc,_pd];}else{var _pf=new T(function(){return E(E(_pe[1])[1]);});return [0,_2U,[1,[0,_pf,new T(function(){var _pg=E(_pf),_ph=_pg[1],_pi=E(E(_p5)[1]),_pj=_pi[1],_pk=E(_pi[2]),_pl=E(_pg[2]),_pm=_pk-_pl;if(!_pm){var _pn=E(_pj),_po=E(_ph),_pp=_pn-_po;if(!_pp){return [0,_pn,_pl];}else{if(_pp<=0){if(0<= -_pp){return [0,_pn,_pl];}else{return [0,_po,_pk];}}else{if(0<=_pp){return [0,_pn,_pl];}else{return [0,_po,_pk];}}}}else{if(_pm<=0){var _pq=E(_pj),_pr=E(_ph),_ps=_pq-_pr;if(!_ps){if( -_pm<=0){return [0,_pq,_pl];}else{return [0,_pr,_pk];}}else{if(_ps<=0){if( -_pm<= -_ps){return [0,_pq,_pl];}else{return [0,_pr,_pk];}}else{if( -_pm<=_ps){return [0,_pq,_pl];}else{return [0,_pr,_pk];}}}}else{var _pt=E(_pj),_pu=E(_ph),_pv=_pt-_pu;if(!_pv){return [0,_pu,_pk];}else{if(_pv<=0){if(_pm<= -_pv){return [0,_pt,_pl];}else{return [0,_pu,_pk];}}else{if(_pm<=_pv){return [0,_pt,_pl];}else{return [0,_pu,_pk];}}}}}}),_3n],_pe[2]],_p8,_p9,_pa,_pb,_pc,_pd];}}},_pw=function(_px,_py,_pz,_){var _pA=function(_pB,_){var _pC=E(_px),_pD=rMV(_pC),_pE=E(_pD),_pF=new T(function(){var _pG=E(E(_pB)[1]);return [0,new T(function(){return B(_oh(_pG[1]));}),new T(function(){return B(_oh(_pG[2]));})];}),_=wMV(_pC,[0,_2U,[1,[0,_pF,_pF,_3n],_pE[2]],_pE[3],_pE[4],_pE[5],_pE[6],_pE[7],_pE[8]]);return new F(function(){return A(_pz,[_]);});},_pH=B(A(_c2,[_6C,_nP,_9g,_py,_o1,_pA,_])),_pI=B(A(_c2,[_6C,_nP,_9g,_py,_o3,function(_pJ,_){var _pK=E(_px),_pL=rMV(_pK),_pM=E(_pL),_pN=B(_p4(_pJ,_pM[1],_pM[2],_pM[3],_pM[4],_pM[5],_pM[6],_pM[7],_pM[8])),_=wMV(_pK,[0,_2W,_pN[2],_pN[3],_pN[4],_pN[5],_pN[6],_pN[7],_pN[8]]);return new F(function(){return A(_pz,[_]);});},_])),_pO=B(A(_c2,[_6C,_nP,_9g,_py,_o2,function(_pP,_){var _pQ=E(_px),_pR=rMV(_pQ),_pS=E(_pR),_pT=B(_p4(_pP,_pS[1],_pS[2],_pS[3],_pS[4],_pS[5],_pS[6],_pS[7],_pS[8])),_=wMV(_pQ,[0,_pT[1],_pT[2],_pT[3],_pT[4],_pT[5],_pT[6],_pT[7],_pT[8]]);return new F(function(){return A(_pz,[_]);});},_]));return _a;},_pU=new T(function(){return document;}),_pV=function(_pW,_){var _pX=E(_pW);if(!_pX[0]){return _3n;}else{var _pY=B(_pV(_pX[2],_));return [1,_pX[1],_pY];}},_pZ=function(_q0,_){var _q1=__arr2lst(0,_q0);return new F(function(){return _pV(_q1,_);});},_q2=(function(e,q){if(!e || typeof e.querySelectorAll !== 'function') {return [];} else {return e.querySelectorAll(q);}}),_q3=function(_q4,_q5,_q6){var _q7=function(_){var _q8=E(_q2)(E(_q5),toJSStr(E(_q6)));return new F(function(){return _pZ(_q8,_);});};return new F(function(){return A(_2,[_q4,_q7]);});},_q9=(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);}),_qa=(function(x){return document.getElementById(x).value;}),_qb=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_qc=new T(function(){return B(err(_qb));}),_qd=function(_qe){var _qf=E(_qe);return (_qf[0]==0)?E(_qc):E(_qf[1]);},_qg=0,_qh=[0,_qg,_qg],_qi=653,_qj=[0,_qi,_qg],_qk=986,_ql=[0,_qi,_qk],_qm=[0,_qg,_qk],_qn=[0,_qh,_qm,_ql,_qj],_qo=[0,_1Q,_qn],_qp=new T(function(){return B(unCStr("NA"));}),_qq=90,_qr=[1,_qq,_3n],_qs=45,_qt=[1,_qs,_qr],_qu=0,_qv=[1,_qu,_qt],_qw=50,_qx=[0,_2W,_3n,_qp,_qu,_qw,_qu,_2M,_qv],_qy=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_qz=new T(function(){return B(err(_qy));}),_qA=new T(function(){return B(unCStr(".json"));}),_qB="saveLink",_qC=new T(function(){return B(unCStr("filePath"));}),_qD=new T(function(){return B(unCStr("input[name=\'mount\']"));}),_qE=new T(function(){return B(unCStr("IndianRoller2.jpg"));}),_qF="loadPath",_qG="filePath",_qH=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_qI=new T(function(){return B(err(_qH));}),_qJ=new T(function(){return B(unCStr("Control.Exception.Base"));}),_qK=new T(function(){return B(unCStr("base"));}),_qL=new T(function(){return B(unCStr("PatternMatchFail"));}),_qM=new T(function(){var _qN=hs_wordToWord64(18445595),_qO=hs_wordToWord64(52003073);return [0,_qN,_qO,[0,_qN,_qO,_qK,_qJ,_qL],_3n,_3n];}),_qP=function(_qQ){return E(_qM);},_qR=function(_qS){var _qT=E(_qS);return new F(function(){return _50(B(_4Y(_qT[1])),_qP,_qT[2]);});},_qU=function(_qV){return E(E(_qV)[1]);},_qW=function(_qX){return [0,_qY,_qX];},_qZ=function(_r0,_r1){return new F(function(){return _16(E(_r0)[1],_r1);});},_r2=function(_r3,_r4){return new F(function(){return _6b(_qZ,_r3,_r4);});},_r5=function(_r6,_r7,_r8){return new F(function(){return _16(E(_r7)[1],_r8);});},_r9=[0,_r5,_qU,_r2],_qY=new T(function(){return [0,_qP,_r9,_qW,_qR,_qU];}),_ra=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_rb=function(_rc){return E(E(_rc)[3]);},_rd=function(_re,_rf){return new F(function(){return die(new T(function(){return B(A(_rb,[_rf,_re]));}));});},_rg=function(_rh,_ri){return new F(function(){return _rd(_rh,_ri);});},_rj=function(_rk,_rl){var _rm=E(_rl);if(!_rm[0]){return [0,_3n,_3n];}else{var _rn=_rm[1];if(!B(A(_rk,[_rn]))){return [0,_3n,_rm];}else{var _ro=new T(function(){var _rp=B(_rj(_rk,_rm[2]));return [0,_rp[1],_rp[2]];});return [0,[1,_rn,new T(function(){return E(E(_ro)[1]);})],new T(function(){return E(E(_ro)[2]);})];}}},_rq=32,_rr=new T(function(){return B(unCStr("\n"));}),_rs=function(_rt){return (E(_rt)==124)?false:true;},_ru=function(_rv,_rw){var _rx=B(_rj(_rs,B(unCStr(_rv)))),_ry=_rx[1],_rz=function(_rA,_rB){var _rC=new T(function(){var _rD=new T(function(){return B(_16(_rw,new T(function(){return B(_16(_rB,_rr));},1)));});return B(unAppCStr(": ",_rD));},1);return new F(function(){return _16(_rA,_rC);});},_rE=E(_rx[2]);if(!_rE[0]){return new F(function(){return _rz(_ry,_3n);});}else{if(E(_rE[1])==124){return new F(function(){return _rz(_ry,[1,_rq,_rE[2]]);});}else{return new F(function(){return _rz(_ry,_3n);});}}},_rF=function(_rG){return new F(function(){return _rg([0,new T(function(){return B(_ru(_rG,_ra));})],_qY);});},_rH=new T(function(){return B(_rF("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_rI=function(_rJ,_rK){while(1){var _rL=B((function(_rM,_rN){var _rO=E(_rM);switch(_rO[0]){case 0:var _rP=E(_rN);if(!_rP[0]){return [0];}else{_rJ=B(A(_rO[1],[_rP[1]]));_rK=_rP[2];return null;}break;case 1:var _rQ=B(A(_rO[1],[_rN])),_rR=_rN;_rJ=_rQ;_rK=_rR;return null;case 2:return [0];case 3:return [1,[0,_rO[1],_rN],new T(function(){return B(_rI(_rO[2],_rN));})];default:return E(_rO[1]);}})(_rJ,_rK));if(_rL!=null){return _rL;}}},_rS=function(_rT,_rU){var _rV=function(_rW){var _rX=E(_rU);if(_rX[0]==3){return [3,_rX[1],new T(function(){return B(_rS(_rT,_rX[2]));})];}else{var _rY=E(_rT);if(_rY[0]==2){return E(_rX);}else{var _rZ=E(_rX);if(_rZ[0]==2){return E(_rY);}else{var _s0=function(_s1){var _s2=E(_rZ);if(_s2[0]==4){return [1,function(_s3){return [4,new T(function(){return B(_16(B(_rI(_rY,_s3)),_s2[1]));})];}];}else{var _s4=E(_rY);if(_s4[0]==1){var _s5=_s4[1],_s6=E(_s2);if(!_s6[0]){return [1,function(_s7){return new F(function(){return _rS(B(A(_s5,[_s7])),_s6);});}];}else{return [1,function(_s8){return new F(function(){return _rS(B(A(_s5,[_s8])),new T(function(){return B(A(_s6[1],[_s8]));}));});}];}}else{var _s9=E(_s2);if(!_s9[0]){return E(_rH);}else{return [1,function(_sa){return new F(function(){return _rS(_s4,new T(function(){return B(A(_s9[1],[_sa]));}));});}];}}}},_sb=E(_rY);switch(_sb[0]){case 1:var _sc=E(_rZ);if(_sc[0]==4){return [1,function(_sd){return [4,new T(function(){return B(_16(B(_rI(B(A(_sb[1],[_sd])),_sd)),_sc[1]));})];}];}else{return new F(function(){return _s0(_);});}break;case 4:var _se=_sb[1],_sf=E(_rZ);switch(_sf[0]){case 0:return [1,function(_sg){return [4,new T(function(){return B(_16(_se,new T(function(){return B(_rI(_sf,_sg));},1)));})];}];case 1:return [1,function(_sh){return [4,new T(function(){return B(_16(_se,new T(function(){return B(_rI(B(A(_sf[1],[_sh])),_sh));},1)));})];}];default:return [4,new T(function(){return B(_16(_se,_sf[1]));})];}break;default:return new F(function(){return _s0(_);});}}}}},_si=E(_rT);switch(_si[0]){case 0:var _sj=E(_rU);if(!_sj[0]){return [0,function(_sk){return new F(function(){return _rS(B(A(_si[1],[_sk])),new T(function(){return B(A(_sj[1],[_sk]));}));});}];}else{return new F(function(){return _rV(_);});}break;case 3:return [3,_si[1],new T(function(){return B(_rS(_si[2],_rU));})];default:return new F(function(){return _rV(_);});}},_sl=new T(function(){return B(unCStr("("));}),_sm=new T(function(){return B(unCStr(")"));}),_sn=function(_so,_sp){while(1){var _sq=E(_so);if(!_sq[0]){return (E(_sp)[0]==0)?true:false;}else{var _sr=E(_sp);if(!_sr[0]){return false;}else{if(E(_sq[1])!=E(_sr[1])){return false;}else{_so=_sq[2];_sp=_sr[2];continue;}}}}},_ss=function(_st,_su){return (!B(_sn(_st,_su)))?true:false;},_sv=[0,_sn,_ss],_sw=function(_sx,_sy){var _sz=E(_sx);switch(_sz[0]){case 0:return [0,function(_sA){return new F(function(){return _sw(B(A(_sz[1],[_sA])),_sy);});}];case 1:return [1,function(_sB){return new F(function(){return _sw(B(A(_sz[1],[_sB])),_sy);});}];case 2:return [2];case 3:return new F(function(){return _rS(B(A(_sy,[_sz[1]])),new T(function(){return B(_sw(_sz[2],_sy));}));});break;default:var _sC=function(_sD){var _sE=E(_sD);if(!_sE[0]){return [0];}else{var _sF=E(_sE[1]);return new F(function(){return _16(B(_rI(B(A(_sy,[_sF[1]])),_sF[2])),new T(function(){return B(_sC(_sE[2]));},1));});}},_sG=B(_sC(_sz[1]));return (_sG[0]==0)?[2]:[4,_sG];}},_sH=[2],_sI=function(_sJ){return [3,_sJ,_sH];},_sK=function(_sL,_sM){var _sN=E(_sL);if(!_sN){return new F(function(){return A(_sM,[_a]);});}else{var _sO=new T(function(){return B(_sK(_sN-1|0,_sM));});return [0,function(_sP){return E(_sO);}];}},_sQ=function(_sR,_sS,_sT){var _sU=new T(function(){return B(A(_sR,[_sI]));}),_sV=function(_sW,_sX,_sY,_sZ){while(1){var _t0=B((function(_t1,_t2,_t3,_t4){var _t5=E(_t1);switch(_t5[0]){case 0:var _t6=E(_t2);if(!_t6[0]){return new F(function(){return A(_sS,[_t4]);});}else{var _t7=_t3+1|0,_t8=_t4;_sW=B(A(_t5[1],[_t6[1]]));_sX=_t6[2];_sY=_t7;_sZ=_t8;return null;}break;case 1:var _t9=B(A(_t5[1],[_t2])),_ta=_t2,_t7=_t3,_t8=_t4;_sW=_t9;_sX=_ta;_sY=_t7;_sZ=_t8;return null;case 2:return new F(function(){return A(_sS,[_t4]);});break;case 3:var _tb=new T(function(){return B(_sw(_t5,_t4));});return new F(function(){return _sK(_t3,function(_tc){return E(_tb);});});break;default:return new F(function(){return _sw(_t5,_t4);});}})(_sW,_sX,_sY,_sZ));if(_t0!=null){return _t0;}}};return function(_td){return new F(function(){return _sV(_sU,_td,0,_sT);});};},_te=function(_tf){return new F(function(){return A(_tf,[_3n]);});},_tg=function(_th,_ti){var _tj=function(_tk){var _tl=E(_tk);if(!_tl[0]){return E(_te);}else{var _tm=_tl[1];if(!B(A(_th,[_tm]))){return E(_te);}else{var _tn=new T(function(){return B(_tj(_tl[2]));}),_to=function(_tp){var _tq=new T(function(){return B(A(_tn,[function(_tr){return new F(function(){return A(_tp,[[1,_tm,_tr]]);});}]));});return [0,function(_ts){return E(_tq);}];};return E(_to);}}};return function(_tt){return new F(function(){return A(_tj,[_tt,_ti]);});};},_tu=[6],_tv=new T(function(){return B(unCStr("valDig: Bad base"));}),_tw=new T(function(){return B(err(_tv));}),_tx=function(_ty,_tz){var _tA=function(_tB,_tC){var _tD=E(_tB);if(!_tD[0]){var _tE=new T(function(){return B(A(_tC,[_3n]));});return function(_tF){return new F(function(){return A(_tF,[_tE]);});};}else{var _tG=E(_tD[1]),_tH=function(_tI){var _tJ=new T(function(){return B(_tA(_tD[2],function(_tK){return new F(function(){return A(_tC,[[1,_tI,_tK]]);});}));}),_tL=function(_tM){var _tN=new T(function(){return B(A(_tJ,[_tM]));});return [0,function(_tO){return E(_tN);}];};return E(_tL);};switch(E(_ty)){case 8:if(48>_tG){var _tP=new T(function(){return B(A(_tC,[_3n]));});return function(_tQ){return new F(function(){return A(_tQ,[_tP]);});};}else{if(_tG>55){var _tR=new T(function(){return B(A(_tC,[_3n]));});return function(_tS){return new F(function(){return A(_tS,[_tR]);});};}else{return new F(function(){return _tH(_tG-48|0);});}}break;case 10:if(48>_tG){var _tT=new T(function(){return B(A(_tC,[_3n]));});return function(_tU){return new F(function(){return A(_tU,[_tT]);});};}else{if(_tG>57){var _tV=new T(function(){return B(A(_tC,[_3n]));});return function(_tW){return new F(function(){return A(_tW,[_tV]);});};}else{return new F(function(){return _tH(_tG-48|0);});}}break;case 16:if(48>_tG){if(97>_tG){if(65>_tG){var _tX=new T(function(){return B(A(_tC,[_3n]));});return function(_tY){return new F(function(){return A(_tY,[_tX]);});};}else{if(_tG>70){var _tZ=new T(function(){return B(A(_tC,[_3n]));});return function(_u0){return new F(function(){return A(_u0,[_tZ]);});};}else{return new F(function(){return _tH((_tG-65|0)+10|0);});}}}else{if(_tG>102){if(65>_tG){var _u1=new T(function(){return B(A(_tC,[_3n]));});return function(_u2){return new F(function(){return A(_u2,[_u1]);});};}else{if(_tG>70){var _u3=new T(function(){return B(A(_tC,[_3n]));});return function(_u4){return new F(function(){return A(_u4,[_u3]);});};}else{return new F(function(){return _tH((_tG-65|0)+10|0);});}}}else{return new F(function(){return _tH((_tG-97|0)+10|0);});}}}else{if(_tG>57){if(97>_tG){if(65>_tG){var _u5=new T(function(){return B(A(_tC,[_3n]));});return function(_u6){return new F(function(){return A(_u6,[_u5]);});};}else{if(_tG>70){var _u7=new T(function(){return B(A(_tC,[_3n]));});return function(_u8){return new F(function(){return A(_u8,[_u7]);});};}else{return new F(function(){return _tH((_tG-65|0)+10|0);});}}}else{if(_tG>102){if(65>_tG){var _u9=new T(function(){return B(A(_tC,[_3n]));});return function(_ua){return new F(function(){return A(_ua,[_u9]);});};}else{if(_tG>70){var _ub=new T(function(){return B(A(_tC,[_3n]));});return function(_uc){return new F(function(){return A(_uc,[_ub]);});};}else{return new F(function(){return _tH((_tG-65|0)+10|0);});}}}else{return new F(function(){return _tH((_tG-97|0)+10|0);});}}}else{return new F(function(){return _tH(_tG-48|0);});}}break;default:return E(_tw);}}},_ud=function(_ue){var _uf=E(_ue);if(!_uf[0]){return [2];}else{return new F(function(){return A(_tz,[_uf]);});}};return function(_ug){return new F(function(){return A(_tA,[_ug,_Q,_ud]);});};},_uh=16,_ui=8,_uj=function(_uk){var _ul=function(_um){return new F(function(){return A(_uk,[[5,[0,_ui,_um]]]);});},_un=function(_uo){return new F(function(){return A(_uk,[[5,[0,_uh,_uo]]]);});},_up=function(_uq){switch(E(_uq)){case 79:return [1,B(_tx(_ui,_ul))];case 88:return [1,B(_tx(_uh,_un))];case 111:return [1,B(_tx(_ui,_ul))];case 120:return [1,B(_tx(_uh,_un))];default:return [2];}};return function(_ur){return (E(_ur)==48)?[0,_up]:[2];};},_us=function(_ut){return [0,B(_uj(_ut))];},_uu=function(_uv){return new F(function(){return A(_uv,[_6t]);});},_uw=function(_ux){return new F(function(){return A(_ux,[_6t]);});},_uy=10,_uz=[0,1],_uA=[0,2147483647],_uB=function(_uC,_uD){while(1){var _uE=E(_uC);if(!_uE[0]){var _uF=_uE[1],_uG=E(_uD);if(!_uG[0]){var _uH=_uG[1],_uI=addC(_uF,_uH);if(!E(_uI[2])){return [0,_uI[1]];}else{_uC=[1,I_fromInt(_uF)];_uD=[1,I_fromInt(_uH)];continue;}}else{_uC=[1,I_fromInt(_uF)];_uD=_uG;continue;}}else{var _uJ=E(_uD);if(!_uJ[0]){_uC=_uE;_uD=[1,I_fromInt(_uJ[1])];continue;}else{return [1,I_add(_uE[1],_uJ[1])];}}}},_uK=new T(function(){return B(_uB(_uA,_uz));}),_uL=function(_uM){var _uN=E(_uM);if(!_uN[0]){var _uO=E(_uN[1]);return (_uO==(-2147483648))?E(_uK):[0, -_uO];}else{return [1,I_negate(_uN[1])];}},_uP=[0,10],_uQ=function(_uR,_uS){while(1){var _uT=E(_uR);if(!_uT[0]){return E(_uS);}else{var _uU=_uS+1|0;_uR=_uT[2];_uS=_uU;continue;}}},_uV=function(_uW){return new F(function(){return _bz(E(_uW));});},_uX=new T(function(){return B(unCStr("this should not happen"));}),_uY=new T(function(){return B(err(_uX));}),_uZ=function(_v0,_v1){while(1){var _v2=E(_v0);if(!_v2[0]){var _v3=_v2[1],_v4=E(_v1);if(!_v4[0]){var _v5=_v4[1];if(!(imul(_v3,_v5)|0)){return [0,imul(_v3,_v5)|0];}else{_v0=[1,I_fromInt(_v3)];_v1=[1,I_fromInt(_v5)];continue;}}else{_v0=[1,I_fromInt(_v3)];_v1=_v4;continue;}}else{var _v6=E(_v1);if(!_v6[0]){_v0=_v2;_v1=[1,I_fromInt(_v6[1])];continue;}else{return [1,I_mul(_v2[1],_v6[1])];}}}},_v7=function(_v8,_v9){var _va=E(_v9);if(!_va[0]){return [0];}else{var _vb=E(_va[2]);return (_vb[0]==0)?E(_uY):[1,B(_uB(B(_uZ(_va[1],_v8)),_vb[1])),new T(function(){return B(_v7(_v8,_vb[2]));})];}},_vc=[0,0],_vd=function(_ve,_vf,_vg){while(1){var _vh=B((function(_vi,_vj,_vk){var _vl=E(_vk);if(!_vl[0]){return E(_vc);}else{if(!E(_vl[2])[0]){return E(_vl[1]);}else{var _vm=E(_vj);if(_vm<=40){var _vn=_vc,_vo=_vl;while(1){var _vp=E(_vo);if(!_vp[0]){return E(_vn);}else{var _vq=B(_uB(B(_uZ(_vn,_vi)),_vp[1]));_vn=_vq;_vo=_vp[2];continue;}}}else{var _vr=B(_uZ(_vi,_vi));if(!(_vm%2)){var _vs=B(_v7(_vi,_vl));_ve=_vr;_vf=quot(_vm+1|0,2);_vg=_vs;return null;}else{var _vs=B(_v7(_vi,[1,_vc,_vl]));_ve=_vr;_vf=quot(_vm+1|0,2);_vg=_vs;return null;}}}}})(_ve,_vf,_vg));if(_vh!=null){return _vh;}}},_vt=function(_vu,_vv){return new F(function(){return _vd(_vu,new T(function(){return B(_uQ(_vv,0));},1),B(_1A(_uV,_vv)));});},_vw=function(_vx){var _vy=new T(function(){var _vz=new T(function(){var _vA=function(_vB){return new F(function(){return A(_vx,[[1,new T(function(){return B(_vt(_uP,_vB));})]]);});};return [1,B(_tx(_uy,_vA))];}),_vC=function(_vD){if(E(_vD)==43){var _vE=function(_vF){return new F(function(){return A(_vx,[[1,new T(function(){return B(_vt(_uP,_vF));})]]);});};return [1,B(_tx(_uy,_vE))];}else{return [2];}},_vG=function(_vH){if(E(_vH)==45){var _vI=function(_vJ){return new F(function(){return A(_vx,[[1,new T(function(){return B(_uL(B(_vt(_uP,_vJ))));})]]);});};return [1,B(_tx(_uy,_vI))];}else{return [2];}};return B(_rS(B(_rS([0,_vG],[0,_vC])),_vz));});return new F(function(){return _rS([0,function(_vK){return (E(_vK)==101)?E(_vy):[2];}],[0,function(_vL){return (E(_vL)==69)?E(_vy):[2];}]);});},_vM=function(_vN){var _vO=function(_vP){return new F(function(){return A(_vN,[[1,_vP]]);});};return function(_vQ){return (E(_vQ)==46)?[1,B(_tx(_uy,_vO))]:[2];};},_vR=function(_vS){return [0,B(_vM(_vS))];},_vT=function(_vU){var _vV=function(_vW){var _vX=function(_vY){return [1,B(_sQ(_vw,_uu,function(_vZ){return new F(function(){return A(_vU,[[5,[1,_vW,_vY,_vZ]]]);});}))];};return [1,B(_sQ(_vR,_uw,_vX))];};return new F(function(){return _tx(_uy,_vV);});},_w0=function(_w1){return [1,B(_vT(_w1))];},_w2=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_w3=function(_w4){return new F(function(){return _f5(_f4,_w4,_w2);});},_w5=false,_w6=true,_w7=function(_w8){var _w9=new T(function(){return B(A(_w8,[_ui]));}),_wa=new T(function(){return B(A(_w8,[_uh]));});return function(_wb){switch(E(_wb)){case 79:return E(_w9);case 88:return E(_wa);case 111:return E(_w9);case 120:return E(_wa);default:return [2];}};},_wc=function(_wd){return [0,B(_w7(_wd))];},_we=function(_wf){return new F(function(){return A(_wf,[_uy]);});},_wg=function(_wh){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_7U(9,_wh,_3n));}))));});},_wi=function(_wj){var _wk=E(_wj);if(!_wk[0]){return E(_wk[1]);}else{return new F(function(){return I_toInt(_wk[1]);});}},_wl=function(_wm,_wn){var _wo=E(_wm);if(!_wo[0]){var _wp=_wo[1],_wq=E(_wn);return (_wq[0]==0)?_wp<=_wq[1]:I_compareInt(_wq[1],_wp)>=0;}else{var _wr=_wo[1],_ws=E(_wn);return (_ws[0]==0)?I_compareInt(_wr,_ws[1])<=0:I_compare(_wr,_ws[1])<=0;}},_wt=function(_wu){return [2];},_wv=function(_ww){var _wx=E(_ww);if(!_wx[0]){return E(_wt);}else{var _wy=_wx[1],_wz=E(_wx[2]);if(!_wz[0]){return E(_wy);}else{var _wA=new T(function(){return B(_wv(_wz));}),_wB=function(_wC){return new F(function(){return _rS(B(A(_wy,[_wC])),new T(function(){return B(A(_wA,[_wC]));}));});};return E(_wB);}}},_wD=function(_wE,_wF){var _wG=function(_wH,_wI,_wJ){var _wK=E(_wH);if(!_wK[0]){return new F(function(){return A(_wJ,[_wE]);});}else{var _wL=E(_wI);if(!_wL[0]){return [2];}else{if(E(_wK[1])!=E(_wL[1])){return [2];}else{var _wM=new T(function(){return B(_wG(_wK[2],_wL[2],_wJ));});return [0,function(_wN){return E(_wM);}];}}}};return function(_wO){return new F(function(){return _wG(_wE,_wO,_wF);});};},_wP=new T(function(){return B(unCStr("SO"));}),_wQ=14,_wR=function(_wS){var _wT=new T(function(){return B(A(_wS,[_wQ]));});return [1,B(_wD(_wP,function(_wU){return E(_wT);}))];},_wV=new T(function(){return B(unCStr("SOH"));}),_wW=1,_wX=function(_wY){var _wZ=new T(function(){return B(A(_wY,[_wW]));});return [1,B(_wD(_wV,function(_x0){return E(_wZ);}))];},_x1=function(_x2){return [1,B(_sQ(_wX,_wR,_x2))];},_x3=new T(function(){return B(unCStr("NUL"));}),_x4=0,_x5=function(_x6){var _x7=new T(function(){return B(A(_x6,[_x4]));});return [1,B(_wD(_x3,function(_x8){return E(_x7);}))];},_x9=new T(function(){return B(unCStr("STX"));}),_xa=2,_xb=function(_xc){var _xd=new T(function(){return B(A(_xc,[_xa]));});return [1,B(_wD(_x9,function(_xe){return E(_xd);}))];},_xf=new T(function(){return B(unCStr("ETX"));}),_xg=3,_xh=function(_xi){var _xj=new T(function(){return B(A(_xi,[_xg]));});return [1,B(_wD(_xf,function(_xk){return E(_xj);}))];},_xl=new T(function(){return B(unCStr("EOT"));}),_xm=4,_xn=function(_xo){var _xp=new T(function(){return B(A(_xo,[_xm]));});return [1,B(_wD(_xl,function(_xq){return E(_xp);}))];},_xr=new T(function(){return B(unCStr("ENQ"));}),_xs=5,_xt=function(_xu){var _xv=new T(function(){return B(A(_xu,[_xs]));});return [1,B(_wD(_xr,function(_xw){return E(_xv);}))];},_xx=new T(function(){return B(unCStr("ACK"));}),_xy=6,_xz=function(_xA){var _xB=new T(function(){return B(A(_xA,[_xy]));});return [1,B(_wD(_xx,function(_xC){return E(_xB);}))];},_xD=new T(function(){return B(unCStr("BEL"));}),_xE=7,_xF=function(_xG){var _xH=new T(function(){return B(A(_xG,[_xE]));});return [1,B(_wD(_xD,function(_xI){return E(_xH);}))];},_xJ=new T(function(){return B(unCStr("BS"));}),_xK=8,_xL=function(_xM){var _xN=new T(function(){return B(A(_xM,[_xK]));});return [1,B(_wD(_xJ,function(_xO){return E(_xN);}))];},_xP=new T(function(){return B(unCStr("HT"));}),_xQ=9,_xR=function(_xS){var _xT=new T(function(){return B(A(_xS,[_xQ]));});return [1,B(_wD(_xP,function(_xU){return E(_xT);}))];},_xV=new T(function(){return B(unCStr("LF"));}),_xW=10,_xX=function(_xY){var _xZ=new T(function(){return B(A(_xY,[_xW]));});return [1,B(_wD(_xV,function(_y0){return E(_xZ);}))];},_y1=new T(function(){return B(unCStr("VT"));}),_y2=11,_y3=function(_y4){var _y5=new T(function(){return B(A(_y4,[_y2]));});return [1,B(_wD(_y1,function(_y6){return E(_y5);}))];},_y7=new T(function(){return B(unCStr("FF"));}),_y8=12,_y9=function(_ya){var _yb=new T(function(){return B(A(_ya,[_y8]));});return [1,B(_wD(_y7,function(_yc){return E(_yb);}))];},_yd=new T(function(){return B(unCStr("CR"));}),_ye=13,_yf=function(_yg){var _yh=new T(function(){return B(A(_yg,[_ye]));});return [1,B(_wD(_yd,function(_yi){return E(_yh);}))];},_yj=new T(function(){return B(unCStr("SI"));}),_yk=15,_yl=function(_ym){var _yn=new T(function(){return B(A(_ym,[_yk]));});return [1,B(_wD(_yj,function(_yo){return E(_yn);}))];},_yp=new T(function(){return B(unCStr("DLE"));}),_yq=16,_yr=function(_ys){var _yt=new T(function(){return B(A(_ys,[_yq]));});return [1,B(_wD(_yp,function(_yu){return E(_yt);}))];},_yv=new T(function(){return B(unCStr("DC1"));}),_yw=17,_yx=function(_yy){var _yz=new T(function(){return B(A(_yy,[_yw]));});return [1,B(_wD(_yv,function(_yA){return E(_yz);}))];},_yB=new T(function(){return B(unCStr("DC2"));}),_yC=18,_yD=function(_yE){var _yF=new T(function(){return B(A(_yE,[_yC]));});return [1,B(_wD(_yB,function(_yG){return E(_yF);}))];},_yH=new T(function(){return B(unCStr("DC3"));}),_yI=19,_yJ=function(_yK){var _yL=new T(function(){return B(A(_yK,[_yI]));});return [1,B(_wD(_yH,function(_yM){return E(_yL);}))];},_yN=new T(function(){return B(unCStr("DC4"));}),_yO=20,_yP=function(_yQ){var _yR=new T(function(){return B(A(_yQ,[_yO]));});return [1,B(_wD(_yN,function(_yS){return E(_yR);}))];},_yT=new T(function(){return B(unCStr("NAK"));}),_yU=21,_yV=function(_yW){var _yX=new T(function(){return B(A(_yW,[_yU]));});return [1,B(_wD(_yT,function(_yY){return E(_yX);}))];},_yZ=new T(function(){return B(unCStr("SYN"));}),_z0=22,_z1=function(_z2){var _z3=new T(function(){return B(A(_z2,[_z0]));});return [1,B(_wD(_yZ,function(_z4){return E(_z3);}))];},_z5=new T(function(){return B(unCStr("ETB"));}),_z6=23,_z7=function(_z8){var _z9=new T(function(){return B(A(_z8,[_z6]));});return [1,B(_wD(_z5,function(_za){return E(_z9);}))];},_zb=new T(function(){return B(unCStr("CAN"));}),_zc=24,_zd=function(_ze){var _zf=new T(function(){return B(A(_ze,[_zc]));});return [1,B(_wD(_zb,function(_zg){return E(_zf);}))];},_zh=new T(function(){return B(unCStr("EM"));}),_zi=25,_zj=function(_zk){var _zl=new T(function(){return B(A(_zk,[_zi]));});return [1,B(_wD(_zh,function(_zm){return E(_zl);}))];},_zn=new T(function(){return B(unCStr("SUB"));}),_zo=26,_zp=function(_zq){var _zr=new T(function(){return B(A(_zq,[_zo]));});return [1,B(_wD(_zn,function(_zs){return E(_zr);}))];},_zt=new T(function(){return B(unCStr("ESC"));}),_zu=27,_zv=function(_zw){var _zx=new T(function(){return B(A(_zw,[_zu]));});return [1,B(_wD(_zt,function(_zy){return E(_zx);}))];},_zz=new T(function(){return B(unCStr("FS"));}),_zA=28,_zB=function(_zC){var _zD=new T(function(){return B(A(_zC,[_zA]));});return [1,B(_wD(_zz,function(_zE){return E(_zD);}))];},_zF=new T(function(){return B(unCStr("GS"));}),_zG=29,_zH=function(_zI){var _zJ=new T(function(){return B(A(_zI,[_zG]));});return [1,B(_wD(_zF,function(_zK){return E(_zJ);}))];},_zL=new T(function(){return B(unCStr("RS"));}),_zM=30,_zN=function(_zO){var _zP=new T(function(){return B(A(_zO,[_zM]));});return [1,B(_wD(_zL,function(_zQ){return E(_zP);}))];},_zR=new T(function(){return B(unCStr("US"));}),_zS=31,_zT=function(_zU){var _zV=new T(function(){return B(A(_zU,[_zS]));});return [1,B(_wD(_zR,function(_zW){return E(_zV);}))];},_zX=new T(function(){return B(unCStr("SP"));}),_zY=32,_zZ=function(_A0){var _A1=new T(function(){return B(A(_A0,[_zY]));});return [1,B(_wD(_zX,function(_A2){return E(_A1);}))];},_A3=new T(function(){return B(unCStr("DEL"));}),_A4=127,_A5=function(_A6){var _A7=new T(function(){return B(A(_A6,[_A4]));});return [1,B(_wD(_A3,function(_A8){return E(_A7);}))];},_A9=[1,_A5,_3n],_Aa=[1,_zZ,_A9],_Ab=[1,_zT,_Aa],_Ac=[1,_zN,_Ab],_Ad=[1,_zH,_Ac],_Ae=[1,_zB,_Ad],_Af=[1,_zv,_Ae],_Ag=[1,_zp,_Af],_Ah=[1,_zj,_Ag],_Ai=[1,_zd,_Ah],_Aj=[1,_z7,_Ai],_Ak=[1,_z1,_Aj],_Al=[1,_yV,_Ak],_Am=[1,_yP,_Al],_An=[1,_yJ,_Am],_Ao=[1,_yD,_An],_Ap=[1,_yx,_Ao],_Aq=[1,_yr,_Ap],_Ar=[1,_yl,_Aq],_As=[1,_yf,_Ar],_At=[1,_y9,_As],_Au=[1,_y3,_At],_Av=[1,_xX,_Au],_Aw=[1,_xR,_Av],_Ax=[1,_xL,_Aw],_Ay=[1,_xF,_Ax],_Az=[1,_xz,_Ay],_AA=[1,_xt,_Az],_AB=[1,_xn,_AA],_AC=[1,_xh,_AB],_AD=[1,_xb,_AC],_AE=[1,_x5,_AD],_AF=[1,_x1,_AE],_AG=new T(function(){return B(_wv(_AF));}),_AH=34,_AI=[0,1114111],_AJ=92,_AK=39,_AL=function(_AM){var _AN=new T(function(){return B(A(_AM,[_xE]));}),_AO=new T(function(){return B(A(_AM,[_xK]));}),_AP=new T(function(){return B(A(_AM,[_xQ]));}),_AQ=new T(function(){return B(A(_AM,[_xW]));}),_AR=new T(function(){return B(A(_AM,[_y2]));}),_AS=new T(function(){return B(A(_AM,[_y8]));}),_AT=new T(function(){return B(A(_AM,[_ye]));}),_AU=new T(function(){return B(A(_AM,[_AJ]));}),_AV=new T(function(){return B(A(_AM,[_AK]));}),_AW=new T(function(){return B(A(_AM,[_AH]));}),_AX=new T(function(){var _AY=function(_AZ){var _B0=new T(function(){return B(_bz(E(_AZ)));}),_B1=function(_B2){var _B3=B(_vt(_B0,_B2));if(!B(_wl(_B3,_AI))){return [2];}else{return new F(function(){return A(_AM,[new T(function(){var _B4=B(_wi(_B3));if(_B4>>>0>1114111){return B(_wg(_B4));}else{return _B4;}})]);});}};return [1,B(_tx(_AZ,_B1))];},_B5=new T(function(){var _B6=new T(function(){return B(A(_AM,[_zS]));}),_B7=new T(function(){return B(A(_AM,[_zM]));}),_B8=new T(function(){return B(A(_AM,[_zG]));}),_B9=new T(function(){return B(A(_AM,[_zA]));}),_Ba=new T(function(){return B(A(_AM,[_zu]));}),_Bb=new T(function(){return B(A(_AM,[_zo]));}),_Bc=new T(function(){return B(A(_AM,[_zi]));}),_Bd=new T(function(){return B(A(_AM,[_zc]));}),_Be=new T(function(){return B(A(_AM,[_z6]));}),_Bf=new T(function(){return B(A(_AM,[_z0]));}),_Bg=new T(function(){return B(A(_AM,[_yU]));}),_Bh=new T(function(){return B(A(_AM,[_yO]));}),_Bi=new T(function(){return B(A(_AM,[_yI]));}),_Bj=new T(function(){return B(A(_AM,[_yC]));}),_Bk=new T(function(){return B(A(_AM,[_yw]));}),_Bl=new T(function(){return B(A(_AM,[_yq]));}),_Bm=new T(function(){return B(A(_AM,[_yk]));}),_Bn=new T(function(){return B(A(_AM,[_wQ]));}),_Bo=new T(function(){return B(A(_AM,[_xy]));}),_Bp=new T(function(){return B(A(_AM,[_xs]));}),_Bq=new T(function(){return B(A(_AM,[_xm]));}),_Br=new T(function(){return B(A(_AM,[_xg]));}),_Bs=new T(function(){return B(A(_AM,[_xa]));}),_Bt=new T(function(){return B(A(_AM,[_wW]));}),_Bu=new T(function(){return B(A(_AM,[_x4]));}),_Bv=function(_Bw){switch(E(_Bw)){case 64:return E(_Bu);case 65:return E(_Bt);case 66:return E(_Bs);case 67:return E(_Br);case 68:return E(_Bq);case 69:return E(_Bp);case 70:return E(_Bo);case 71:return E(_AN);case 72:return E(_AO);case 73:return E(_AP);case 74:return E(_AQ);case 75:return E(_AR);case 76:return E(_AS);case 77:return E(_AT);case 78:return E(_Bn);case 79:return E(_Bm);case 80:return E(_Bl);case 81:return E(_Bk);case 82:return E(_Bj);case 83:return E(_Bi);case 84:return E(_Bh);case 85:return E(_Bg);case 86:return E(_Bf);case 87:return E(_Be);case 88:return E(_Bd);case 89:return E(_Bc);case 90:return E(_Bb);case 91:return E(_Ba);case 92:return E(_B9);case 93:return E(_B8);case 94:return E(_B7);case 95:return E(_B6);default:return [2];}};return B(_rS([0,function(_Bx){return (E(_Bx)==94)?[0,_Bv]:[2];}],new T(function(){return B(A(_AG,[_AM]));})));});return B(_rS([1,B(_sQ(_wc,_we,_AY))],_B5));});return new F(function(){return _rS([0,function(_By){switch(E(_By)){case 34:return E(_AW);case 39:return E(_AV);case 92:return E(_AU);case 97:return E(_AN);case 98:return E(_AO);case 102:return E(_AS);case 110:return E(_AQ);case 114:return E(_AT);case 116:return E(_AP);case 118:return E(_AR);default:return [2];}}],_AX);});},_Bz=function(_BA){return new F(function(){return A(_BA,[_a]);});},_BB=function(_BC){var _BD=E(_BC);if(!_BD[0]){return E(_Bz);}else{var _BE=E(_BD[1]),_BF=_BE>>>0,_BG=new T(function(){return B(_BB(_BD[2]));});if(_BF>887){var _BH=u_iswspace(_BE);if(!E(_BH)){return E(_Bz);}else{var _BI=function(_BJ){var _BK=new T(function(){return B(A(_BG,[_BJ]));});return [0,function(_BL){return E(_BK);}];};return E(_BI);}}else{var _BM=E(_BF);if(_BM==32){var _BN=function(_BO){var _BP=new T(function(){return B(A(_BG,[_BO]));});return [0,function(_BQ){return E(_BP);}];};return E(_BN);}else{if(_BM-9>>>0>4){if(E(_BM)==160){var _BR=function(_BS){var _BT=new T(function(){return B(A(_BG,[_BS]));});return [0,function(_BU){return E(_BT);}];};return E(_BR);}else{return E(_Bz);}}else{var _BV=function(_BW){var _BX=new T(function(){return B(A(_BG,[_BW]));});return [0,function(_BY){return E(_BX);}];};return E(_BV);}}}}},_BZ=function(_C0){var _C1=new T(function(){return B(_BZ(_C0));}),_C2=function(_C3){return (E(_C3)==92)?E(_C1):[2];},_C4=function(_C5){return [0,_C2];},_C6=[1,function(_C7){return new F(function(){return A(_BB,[_C7,_C4]);});}],_C8=new T(function(){return B(_AL(function(_C9){return new F(function(){return A(_C0,[[0,_C9,_w6]]);});}));}),_Ca=function(_Cb){var _Cc=E(_Cb);if(_Cc==38){return E(_C1);}else{var _Cd=_Cc>>>0;if(_Cd>887){var _Ce=u_iswspace(_Cc);return (E(_Ce)==0)?[2]:E(_C6);}else{var _Cf=E(_Cd);return (_Cf==32)?E(_C6):(_Cf-9>>>0>4)?(E(_Cf)==160)?E(_C6):[2]:E(_C6);}}};return new F(function(){return _rS([0,function(_Cg){return (E(_Cg)==92)?[0,_Ca]:[2];}],[0,function(_Ch){var _Ci=E(_Ch);if(E(_Ci)==92){return E(_C8);}else{return new F(function(){return A(_C0,[[0,_Ci,_w5]]);});}}]);});},_Cj=function(_Ck,_Cl){var _Cm=new T(function(){return B(A(_Cl,[[1,new T(function(){return B(A(_Ck,[_3n]));})]]));}),_Cn=function(_Co){var _Cp=E(_Co),_Cq=E(_Cp[1]);if(E(_Cq)==34){if(!E(_Cp[2])){return E(_Cm);}else{return new F(function(){return _Cj(function(_Cr){return new F(function(){return A(_Ck,[[1,_Cq,_Cr]]);});},_Cl);});}}else{return new F(function(){return _Cj(function(_Cs){return new F(function(){return A(_Ck,[[1,_Cq,_Cs]]);});},_Cl);});}};return new F(function(){return _BZ(_Cn);});},_Ct=new T(function(){return B(unCStr("_\'"));}),_Cu=function(_Cv){var _Cw=u_iswalnum(_Cv);if(!E(_Cw)){return new F(function(){return _f5(_f4,_Cv,_Ct);});}else{return true;}},_Cx=function(_Cy){return new F(function(){return _Cu(E(_Cy));});},_Cz=new T(function(){return B(unCStr(",;()[]{}`"));}),_CA=new T(function(){return B(unCStr("=>"));}),_CB=[1,_CA,_3n],_CC=new T(function(){return B(unCStr("~"));}),_CD=[1,_CC,_CB],_CE=new T(function(){return B(unCStr("@"));}),_CF=[1,_CE,_CD],_CG=new T(function(){return B(unCStr("->"));}),_CH=[1,_CG,_CF],_CI=new T(function(){return B(unCStr("<-"));}),_CJ=[1,_CI,_CH],_CK=new T(function(){return B(unCStr("|"));}),_CL=[1,_CK,_CJ],_CM=new T(function(){return B(unCStr("\\"));}),_CN=[1,_CM,_CL],_CO=new T(function(){return B(unCStr("="));}),_CP=[1,_CO,_CN],_CQ=new T(function(){return B(unCStr("::"));}),_CR=[1,_CQ,_CP],_CS=new T(function(){return B(unCStr(".."));}),_CT=[1,_CS,_CR],_CU=function(_CV){var _CW=new T(function(){return B(A(_CV,[_tu]));}),_CX=new T(function(){var _CY=new T(function(){var _CZ=function(_D0){var _D1=new T(function(){return B(A(_CV,[[0,_D0]]));});return [0,function(_D2){return (E(_D2)==39)?E(_D1):[2];}];};return B(_AL(_CZ));}),_D3=function(_D4){var _D5=E(_D4);switch(E(_D5)){case 39:return [2];case 92:return E(_CY);default:var _D6=new T(function(){return B(A(_CV,[[0,_D5]]));});return [0,function(_D7){return (E(_D7)==39)?E(_D6):[2];}];}},_D8=new T(function(){var _D9=new T(function(){return B(_Cj(_Q,_CV));}),_Da=new T(function(){var _Db=new T(function(){var _Dc=new T(function(){var _Dd=function(_De){var _Df=E(_De),_Dg=u_iswalpha(_Df);return (E(_Dg)==0)?(E(_Df)==95)?[1,B(_tg(_Cx,function(_Dh){return new F(function(){return A(_CV,[[3,[1,_Df,_Dh]]]);});}))]:[2]:[1,B(_tg(_Cx,function(_Di){return new F(function(){return A(_CV,[[3,[1,_Df,_Di]]]);});}))];};return B(_rS([0,_Dd],new T(function(){return [1,B(_sQ(_us,_w0,_CV))];})));}),_Dj=function(_Dk){return (!B(_f5(_f4,_Dk,_w2)))?[2]:[1,B(_tg(_w3,function(_Dl){var _Dm=[1,_Dk,_Dl];if(!B(_f5(_sv,_Dm,_CT))){return new F(function(){return A(_CV,[[4,_Dm]]);});}else{return new F(function(){return A(_CV,[[2,_Dm]]);});}}))];};return B(_rS([0,_Dj],_Dc));});return B(_rS([0,function(_Dn){if(!B(_f5(_f4,_Dn,_Cz))){return [2];}else{return new F(function(){return A(_CV,[[2,[1,_Dn,_3n]]]);});}}],_Db));});return B(_rS([0,function(_Do){return (E(_Do)==34)?E(_D9):[2];}],_Da));});return B(_rS([0,function(_Dp){return (E(_Dp)==39)?[0,_D3]:[2];}],_D8));});return new F(function(){return _rS([1,function(_Dq){return (E(_Dq)[0]==0)?E(_CW):[2];}],_CX);});},_Dr=0,_Ds=function(_Dt,_Du){var _Dv=new T(function(){var _Dw=new T(function(){var _Dx=function(_Dy){var _Dz=new T(function(){var _DA=new T(function(){return B(A(_Du,[_Dy]));});return B(_CU(function(_DB){var _DC=E(_DB);return (_DC[0]==2)?(!B(_26(_DC[1],_sm)))?[2]:E(_DA):[2];}));}),_DD=function(_DE){return E(_Dz);};return [1,function(_DF){return new F(function(){return A(_BB,[_DF,_DD]);});}];};return B(A(_Dt,[_Dr,_Dx]));});return B(_CU(function(_DG){var _DH=E(_DG);return (_DH[0]==2)?(!B(_26(_DH[1],_sl)))?[2]:E(_Dw):[2];}));}),_DI=function(_DJ){return E(_Dv);};return function(_DK){return new F(function(){return A(_BB,[_DK,_DI]);});};},_DL=function(_DM,_DN){var _DO=function(_DP){var _DQ=new T(function(){return B(A(_DM,[_DP]));}),_DR=function(_DS){return new F(function(){return _rS(B(A(_DQ,[_DS])),new T(function(){return [1,B(_Ds(_DO,_DS))];}));});};return E(_DR);},_DT=new T(function(){return B(A(_DM,[_DN]));}),_DU=function(_DV){return new F(function(){return _rS(B(A(_DT,[_DV])),new T(function(){return [1,B(_Ds(_DO,_DV))];}));});};return E(_DU);},_DW=function(_DX,_DY){return new F(function(){return A(_DY,[_2K]);});},_DZ=[0,_2P,_DW],_E0=[1,_DZ,_3n],_E1=function(_E2,_E3){return new F(function(){return A(_E3,[_2M]);});},_E4=[0,_2O,_E1],_E5=[1,_E4,_E0],_E6=function(_E7,_E8,_E9){var _Ea=E(_E7);if(!_Ea[0]){return [2];}else{var _Eb=E(_Ea[1]),_Ec=_Eb[1],_Ed=new T(function(){return B(A(_Eb[2],[_E8,_E9]));}),_Ee=new T(function(){return B(_CU(function(_Ef){var _Eg=E(_Ef);switch(_Eg[0]){case 3:return (!B(_26(_Ec,_Eg[1])))?[2]:E(_Ed);case 4:return (!B(_26(_Ec,_Eg[1])))?[2]:E(_Ed);default:return [2];}}));}),_Eh=function(_Ei){return E(_Ee);};return new F(function(){return _rS([1,function(_Ej){return new F(function(){return A(_BB,[_Ej,_Eh]);});}],new T(function(){return B(_E6(_Ea[2],_E8,_E9));}));});}},_Ek=function(_El,_Em){return new F(function(){return _E6(_E5,_El,_Em);});},_En=function(_Eo){var _Ep=function(_Eq){return [3,_Eo,_sH];};return [1,function(_Er){return new F(function(){return A(_BB,[_Er,_Ep]);});}];},_Es=new T(function(){return B(A(_DL,[_Ek,_Dr,_En]));}),_Et=new T(function(){return B(err(_qy));}),_Eu=new T(function(){return B(err(_qH));}),_Ev=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:50:3-15"));}),_Ew=[0,_6t,_6u,_3n,_Ev,_6t,_6t],_Ex=new T(function(){return B(_6r(_Ew));}),_Ey=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:51:3-15"));}),_Ez=[0,_6t,_6u,_3n,_Ey,_6t,_6t],_EA=new T(function(){return B(_6r(_Ez));}),_EB=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:52:3-14"));}),_EC=[0,_6t,_6u,_3n,_EB,_6t,_6t],_ED=new T(function(){return B(_6r(_EC));}),_EE=function(_EF,_EG){var _EH=function(_EI,_EJ){var _EK=function(_EL){return new F(function(){return A(_EJ,[new T(function(){return  -E(_EL);})]);});},_EM=new T(function(){return B(_CU(function(_EN){return new F(function(){return A(_EF,[_EN,_EI,_EK]);});}));}),_EO=function(_EP){return E(_EM);},_EQ=function(_ER){return new F(function(){return A(_BB,[_ER,_EO]);});},_ES=new T(function(){return B(_CU(function(_ET){var _EU=E(_ET);if(_EU[0]==4){var _EV=E(_EU[1]);if(!_EV[0]){return new F(function(){return A(_EF,[_EU,_EI,_EJ]);});}else{if(E(_EV[1])==45){if(!E(_EV[2])[0]){return [1,_EQ];}else{return new F(function(){return A(_EF,[_EU,_EI,_EJ]);});}}else{return new F(function(){return A(_EF,[_EU,_EI,_EJ]);});}}}else{return new F(function(){return A(_EF,[_EU,_EI,_EJ]);});}}));}),_EW=function(_EX){return E(_ES);};return [1,function(_EY){return new F(function(){return A(_BB,[_EY,_EW]);});}];};return new F(function(){return _DL(_EH,_EG);});},_EZ=new T(function(){return 1/0;}),_F0=function(_F1,_F2){return new F(function(){return A(_F2,[_EZ]);});},_F3=new T(function(){return 0/0;}),_F4=function(_F5,_F6){return new F(function(){return A(_F6,[_F3]);});},_F7=new T(function(){return B(unCStr("NaN"));}),_F8=new T(function(){return B(unCStr("Infinity"));}),_F9=1024,_Fa=-1021,_Fb=new T(function(){return B(unCStr("GHC.Exception"));}),_Fc=new T(function(){return B(unCStr("base"));}),_Fd=new T(function(){return B(unCStr("ArithException"));}),_Fe=new T(function(){var _Ff=hs_wordToWord64(4194982440),_Fg=hs_wordToWord64(3110813675);return [0,_Ff,_Fg,[0,_Ff,_Fg,_Fc,_Fb,_Fd],_3n,_3n];}),_Fh=function(_Fi){return E(_Fe);},_Fj=function(_Fk){var _Fl=E(_Fk);return new F(function(){return _50(B(_4Y(_Fl[1])),_Fh,_Fl[2]);});},_Fm=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_Fn=new T(function(){return B(unCStr("denormal"));}),_Fo=new T(function(){return B(unCStr("divide by zero"));}),_Fp=new T(function(){return B(unCStr("loss of precision"));}),_Fq=new T(function(){return B(unCStr("arithmetic underflow"));}),_Fr=new T(function(){return B(unCStr("arithmetic overflow"));}),_Fs=function(_Ft,_Fu){switch(E(_Ft)){case 0:return new F(function(){return _16(_Fr,_Fu);});break;case 1:return new F(function(){return _16(_Fq,_Fu);});break;case 2:return new F(function(){return _16(_Fp,_Fu);});break;case 3:return new F(function(){return _16(_Fo,_Fu);});break;case 4:return new F(function(){return _16(_Fn,_Fu);});break;default:return new F(function(){return _16(_Fm,_Fu);});}},_Fv=function(_Fw){return new F(function(){return _Fs(_Fw,_3n);});},_Fx=function(_Fy,_Fz,_FA){return new F(function(){return _Fs(_Fz,_FA);});},_FB=function(_FC,_FD){return new F(function(){return _6b(_Fs,_FC,_FD);});},_FE=[0,_Fx,_Fv,_FB],_FF=new T(function(){return [0,_Fh,_FE,_FG,_Fj,_Fv];}),_FG=function(_ri){return [0,_FF,_ri];},_FH=3,_FI=new T(function(){return B(_FG(_FH));}),_FJ=new T(function(){return die(_FI);}),_FK=function(_FL,_FM){var _FN=E(_FL);if(!_FN[0]){var _FO=_FN[1],_FP=E(_FM);return (_FP[0]==0)?_FO==_FP[1]:(I_compareInt(_FP[1],_FO)==0)?true:false;}else{var _FQ=_FN[1],_FR=E(_FM);return (_FR[0]==0)?(I_compareInt(_FQ,_FR[1])==0)?true:false:(I_compare(_FQ,_FR[1])==0)?true:false;}},_FS=[0,0],_FT=function(_FU,_FV){while(1){var _FW=E(_FU);if(!_FW[0]){var _FX=E(_FW[1]);if(_FX==(-2147483648)){_FU=[1,I_fromInt(-2147483648)];continue;}else{var _FY=E(_FV);if(!_FY[0]){return [0,_FX%_FY[1]];}else{_FU=[1,I_fromInt(_FX)];_FV=_FY;continue;}}}else{var _FZ=_FW[1],_G0=E(_FV);return (_G0[0]==0)?[1,I_rem(_FZ,I_fromInt(_G0[1]))]:[1,I_rem(_FZ,_G0[1])];}}},_G1=function(_G2,_G3){if(!B(_FK(_G3,_FS))){return new F(function(){return _FT(_G2,_G3);});}else{return E(_FJ);}},_G4=function(_G5,_G6){while(1){if(!B(_FK(_G6,_FS))){var _G7=_G6,_G8=B(_G1(_G5,_G6));_G5=_G7;_G6=_G8;continue;}else{return E(_G5);}}},_G9=function(_Ga){var _Gb=E(_Ga);if(!_Gb[0]){var _Gc=E(_Gb[1]);return (_Gc==(-2147483648))?E(_uK):(_Gc<0)?[0, -_Gc]:E(_Gb);}else{var _Gd=_Gb[1];return (I_compareInt(_Gd,0)>=0)?E(_Gb):[1,I_negate(_Gd)];}},_Ge=function(_Gf,_Gg){while(1){var _Gh=E(_Gf);if(!_Gh[0]){var _Gi=E(_Gh[1]);if(_Gi==(-2147483648)){_Gf=[1,I_fromInt(-2147483648)];continue;}else{var _Gj=E(_Gg);if(!_Gj[0]){return [0,quot(_Gi,_Gj[1])];}else{_Gf=[1,I_fromInt(_Gi)];_Gg=_Gj;continue;}}}else{var _Gk=_Gh[1],_Gl=E(_Gg);return (_Gl[0]==0)?[0,I_toInt(I_quot(_Gk,I_fromInt(_Gl[1])))]:[1,I_quot(_Gk,_Gl[1])];}}},_Gm=5,_Gn=new T(function(){return B(_FG(_Gm));}),_Go=new T(function(){return die(_Gn);}),_Gp=function(_Gq,_Gr){if(!B(_FK(_Gr,_FS))){var _Gs=B(_G4(B(_G9(_Gq)),B(_G9(_Gr))));return (!B(_FK(_Gs,_FS)))?[0,B(_Ge(_Gq,_Gs)),B(_Ge(_Gr,_Gs))]:E(_FJ);}else{return E(_Go);}},_Gt=[0,1],_Gu=new T(function(){return B(unCStr("Negative exponent"));}),_Gv=new T(function(){return B(err(_Gu));}),_Gw=[0,2],_Gx=new T(function(){return B(_FK(_Gw,_FS));}),_Gy=function(_Gz,_GA){while(1){var _GB=E(_Gz);if(!_GB[0]){var _GC=_GB[1],_GD=E(_GA);if(!_GD[0]){var _GE=_GD[1],_GF=subC(_GC,_GE);if(!E(_GF[2])){return [0,_GF[1]];}else{_Gz=[1,I_fromInt(_GC)];_GA=[1,I_fromInt(_GE)];continue;}}else{_Gz=[1,I_fromInt(_GC)];_GA=_GD;continue;}}else{var _GG=E(_GA);if(!_GG[0]){_Gz=_GB;_GA=[1,I_fromInt(_GG[1])];continue;}else{return [1,I_sub(_GB[1],_GG[1])];}}}},_GH=function(_GI,_GJ,_GK){while(1){if(!E(_Gx)){if(!B(_FK(B(_FT(_GJ,_Gw)),_FS))){if(!B(_FK(_GJ,_Gt))){var _GL=B(_uZ(_GI,_GI)),_GM=B(_Ge(B(_Gy(_GJ,_Gt)),_Gw)),_GN=B(_uZ(_GI,_GK));_GI=_GL;_GJ=_GM;_GK=_GN;continue;}else{return new F(function(){return _uZ(_GI,_GK);});}}else{var _GL=B(_uZ(_GI,_GI)),_GM=B(_Ge(_GJ,_Gw));_GI=_GL;_GJ=_GM;continue;}}else{return E(_FJ);}}},_GO=function(_GP,_GQ){while(1){if(!E(_Gx)){if(!B(_FK(B(_FT(_GQ,_Gw)),_FS))){if(!B(_FK(_GQ,_Gt))){return new F(function(){return _GH(B(_uZ(_GP,_GP)),B(_Ge(B(_Gy(_GQ,_Gt)),_Gw)),_GP);});}else{return E(_GP);}}else{var _GR=B(_uZ(_GP,_GP)),_GS=B(_Ge(_GQ,_Gw));_GP=_GR;_GQ=_GS;continue;}}else{return E(_FJ);}}},_GT=function(_GU,_GV){if(!B(_fs(_GV,_FS))){if(!B(_FK(_GV,_FS))){return new F(function(){return _GO(_GU,_GV);});}else{return E(_Gt);}}else{return E(_Gv);}},_GW=[0,1],_GX=[0,0],_GY=[0,-1],_GZ=function(_H0){var _H1=E(_H0);if(!_H1[0]){var _H2=_H1[1];return (_H2>=0)?(E(_H2)==0)?E(_GX):E(_uz):E(_GY);}else{var _H3=I_compareInt(_H1[1],0);return (_H3<=0)?(E(_H3)==0)?E(_GX):E(_GY):E(_uz);}},_H4=function(_H5,_H6,_H7){while(1){var _H8=E(_H7);if(!_H8[0]){if(!B(_fs(_H5,_vc))){return [0,B(_uZ(_H6,B(_GT(_uP,_H5)))),_Gt];}else{var _H9=B(_GT(_uP,B(_uL(_H5))));return new F(function(){return _Gp(B(_uZ(_H6,B(_GZ(_H9)))),B(_G9(_H9)));});}}else{var _Ha=B(_Gy(_H5,_GW)),_Hb=B(_uB(B(_uZ(_H6,_uP)),B(_bz(E(_H8[1])))));_H5=_Ha;_H6=_Hb;_H7=_H8[2];continue;}}},_Hc=function(_Hd,_He){var _Hf=E(_Hd);if(!_Hf[0]){var _Hg=_Hf[1],_Hh=E(_He);return (_Hh[0]==0)?_Hg>=_Hh[1]:I_compareInt(_Hh[1],_Hg)<=0;}else{var _Hi=_Hf[1],_Hj=E(_He);return (_Hj[0]==0)?I_compareInt(_Hi,_Hj[1])>=0:I_compare(_Hi,_Hj[1])>=0;}},_Hk=function(_Hl){var _Hm=E(_Hl);if(!_Hm[0]){var _Hn=_Hm[2];return new F(function(){return _Gp(B(_uZ(B(_vd(new T(function(){return B(_bz(E(_Hm[1])));}),new T(function(){return B(_uQ(_Hn,0));},1),B(_1A(_uV,_Hn)))),_GW)),_GW);});}else{var _Ho=_Hm[1],_Hp=_Hm[3],_Hq=E(_Hm[2]);if(!_Hq[0]){var _Hr=E(_Hp);if(!_Hr[0]){return new F(function(){return _Gp(B(_uZ(B(_vt(_uP,_Ho)),_GW)),_GW);});}else{var _Hs=_Hr[1];if(!B(_Hc(_Hs,_vc))){var _Ht=B(_GT(_uP,B(_uL(_Hs))));return new F(function(){return _Gp(B(_uZ(B(_vt(_uP,_Ho)),B(_GZ(_Ht)))),B(_G9(_Ht)));});}else{return new F(function(){return _Gp(B(_uZ(B(_uZ(B(_vt(_uP,_Ho)),B(_GT(_uP,_Hs)))),_GW)),_GW);});}}}else{var _Hu=_Hq[1],_Hv=E(_Hp);if(!_Hv[0]){return new F(function(){return _H4(_vc,B(_vt(_uP,_Ho)),_Hu);});}else{return new F(function(){return _H4(_Hv[1],B(_vt(_uP,_Ho)),_Hu);});}}}},_Hw=function(_Hx,_Hy){while(1){var _Hz=E(_Hy);if(!_Hz[0]){return [0];}else{if(!B(A(_Hx,[_Hz[1]]))){return E(_Hz);}else{_Hy=_Hz[2];continue;}}}},_HA=function(_HB,_HC){var _HD=E(_HB);if(!_HD[0]){var _HE=_HD[1],_HF=E(_HC);return (_HF[0]==0)?_HE>_HF[1]:I_compareInt(_HF[1],_HE)<0;}else{var _HG=_HD[1],_HH=E(_HC);return (_HH[0]==0)?I_compareInt(_HG,_HH[1])>0:I_compare(_HG,_HH[1])>0;}},_HI=0,_HJ=function(_HK,_HL){return E(_HK)==E(_HL);},_HM=function(_HN){return new F(function(){return _HJ(_HI,_HN);});},_HO=[0,E(_vc),E(_Gt)],_HP=[1,_HO],_HQ=[0,-2147483648],_HR=[0,2147483647],_HS=function(_HT,_HU,_HV){var _HW=E(_HV);if(!_HW[0]){return [1,new T(function(){var _HX=B(_Hk(_HW));return [0,E(_HX[1]),E(_HX[2])];})];}else{var _HY=E(_HW[3]);if(!_HY[0]){return [1,new T(function(){var _HZ=B(_Hk(_HW));return [0,E(_HZ[1]),E(_HZ[2])];})];}else{var _I0=_HY[1];if(!B(_HA(_I0,_HR))){if(!B(_fs(_I0,_HQ))){var _I1=function(_I2){var _I3=_I2+B(_wi(_I0))|0;return (_I3<=(E(_HU)+3|0))?(_I3>=(E(_HT)-3|0))?[1,new T(function(){var _I4=B(_Hk(_HW));return [0,E(_I4[1]),E(_I4[2])];})]:E(_HP):[0];},_I5=B(_Hw(_HM,_HW[1]));if(!_I5[0]){var _I6=E(_HW[2]);if(!_I6[0]){return E(_HP);}else{var _I7=B(_rj(_HM,_I6[1]));if(!E(_I7[2])[0]){return E(_HP);}else{return new F(function(){return _I1( -B(_uQ(_I7[1],0)));});}}}else{return new F(function(){return _I1(B(_uQ(_I5,0)));});}}else{return [0];}}else{return [0];}}}},_I8=function(_I9,_Ia){return [2];},_Ib=[0,1],_Ic=function(_Id,_Ie){var _If=E(_Id);if(!_If[0]){var _Ig=_If[1],_Ih=E(_Ie);if(!_Ih[0]){var _Ii=_Ih[1];return (_Ig!=_Ii)?(_Ig>_Ii)?2:0:1;}else{var _Ij=I_compareInt(_Ih[1],_Ig);return (_Ij<=0)?(_Ij>=0)?1:2:0;}}else{var _Ik=_If[1],_Il=E(_Ie);if(!_Il[0]){var _Im=I_compareInt(_Ik,_Il[1]);return (_Im>=0)?(_Im<=0)?1:2:0;}else{var _In=I_compare(_Ik,_Il[1]);return (_In>=0)?(_In<=0)?1:2:0;}}},_Io=function(_Ip,_Iq){var _Ir=E(_Ip);return (_Ir[0]==0)?_Ir[1]*Math.pow(2,_Iq):I_toNumber(_Ir[1])*Math.pow(2,_Iq);},_Is=function(_It,_Iu){while(1){var _Iv=E(_It);if(!_Iv[0]){var _Iw=E(_Iv[1]);if(_Iw==(-2147483648)){_It=[1,I_fromInt(-2147483648)];continue;}else{var _Ix=E(_Iu);if(!_Ix[0]){var _Iy=_Ix[1];return [0,[0,quot(_Iw,_Iy)],[0,_Iw%_Iy]];}else{_It=[1,I_fromInt(_Iw)];_Iu=_Ix;continue;}}}else{var _Iz=E(_Iu);if(!_Iz[0]){_It=_Iv;_Iu=[1,I_fromInt(_Iz[1])];continue;}else{var _IA=I_quotRem(_Iv[1],_Iz[1]);return [0,[1,_IA[1]],[1,_IA[2]]];}}}},_IB=[0,0],_IC=function(_ID,_IE,_IF){if(!B(_FK(_IF,_IB))){var _IG=B(_Is(_IE,_IF)),_IH=_IG[1];switch(B(_Ic(B(_cz(_IG[2],1)),_IF))){case 0:return new F(function(){return _Io(_IH,_ID);});break;case 1:if(!(B(_wi(_IH))&1)){return new F(function(){return _Io(_IH,_ID);});}else{return new F(function(){return _Io(B(_uB(_IH,_Ib)),_ID);});}break;default:return new F(function(){return _Io(B(_uB(_IH,_Ib)),_ID);});}}else{return E(_FJ);}},_II=function(_IJ){var _IK=_uz,_IL=0;while(1){if(!B(_fs(_IK,_IJ))){if(!B(_HA(_IK,_IJ))){if(!B(_FK(_IK,_IJ))){return new F(function(){return _rF("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_IL);}}else{return _IL-1|0;}}else{var _IM=B(_cz(_IK,1)),_IN=_IL+1|0;_IK=_IM;_IL=_IN;continue;}}},_IO=function(_IP){var _IQ=E(_IP);if(!_IQ[0]){var _IR=_IQ[1]>>>0;if(!_IR){return -1;}else{var _IS=1,_IT=0;while(1){if(_IS>=_IR){if(_IS<=_IR){if(_IS!=_IR){return new F(function(){return _rF("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_IT);}}else{return _IT-1|0;}}else{var _IU=imul(_IS,2)>>>0,_IV=_IT+1|0;_IS=_IU;_IT=_IV;continue;}}}}else{return new F(function(){return _II(_IQ);});}},_IW=function(_IX){var _IY=E(_IX);if(!_IY[0]){var _IZ=_IY[1]>>>0;if(!_IZ){return [0,-1,0];}else{var _J0=function(_J1,_J2){while(1){if(_J1>=_IZ){if(_J1<=_IZ){if(_J1!=_IZ){return new F(function(){return _rF("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_J2);}}else{return _J2-1|0;}}else{var _J3=imul(_J1,2)>>>0,_J4=_J2+1|0;_J1=_J3;_J2=_J4;continue;}}};return [0,B(_J0(1,0)),(_IZ&_IZ-1>>>0)>>>0&4294967295];}}else{var _J5=B(_IO(_IY)),_J6=_J5>>>0;if(!_J6){var _J7=E(_J5);return (_J7==(-2))?[0,-2,0]:[0,_J7,1];}else{var _J8=function(_J9,_Ja){while(1){if(_J9>=_J6){if(_J9<=_J6){if(_J9!=_J6){return new F(function(){return _rF("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_Ja);}}else{return _Ja-1|0;}}else{var _Jb=imul(_J9,2)>>>0,_Jc=_Ja+1|0;_J9=_Jb;_Ja=_Jc;continue;}}},_Jd=B(_J8(1,0));return ((_Jd+_Jd|0)!=_J5)?[0,_J5,1]:[0,_J5,0];}}},_Je=function(_Jf,_Jg){while(1){var _Jh=E(_Jf);if(!_Jh[0]){var _Ji=_Jh[1],_Jj=E(_Jg);if(!_Jj[0]){return [0,(_Ji>>>0&_Jj[1]>>>0)>>>0&4294967295];}else{_Jf=[1,I_fromInt(_Ji)];_Jg=_Jj;continue;}}else{var _Jk=E(_Jg);if(!_Jk[0]){_Jf=_Jh;_Jg=[1,I_fromInt(_Jk[1])];continue;}else{return [1,I_and(_Jh[1],_Jk[1])];}}}},_Jl=[0,2],_Jm=function(_Jn,_Jo){var _Jp=E(_Jn);if(!_Jp[0]){var _Jq=(_Jp[1]>>>0&(2<<_Jo>>>0)-1>>>0)>>>0,_Jr=1<<_Jo>>>0;return (_Jr<=_Jq)?(_Jr>=_Jq)?1:2:0;}else{var _Js=B(_Je(_Jp,B(_Gy(B(_cz(_Jl,_Jo)),_uz)))),_Jt=B(_cz(_uz,_Jo));return (!B(_HA(_Jt,_Js)))?(!B(_fs(_Jt,_Js)))?1:2:0;}},_Ju=function(_Jv,_Jw){while(1){var _Jx=E(_Jv);if(!_Jx[0]){_Jv=[1,I_fromInt(_Jx[1])];continue;}else{return [1,I_shiftRight(_Jx[1],_Jw)];}}},_Jy=function(_Jz,_JA,_JB,_JC){var _JD=B(_IW(_JC)),_JE=_JD[1];if(!E(_JD[2])){var _JF=B(_IO(_JB));if(_JF<((_JE+_Jz|0)-1|0)){var _JG=_JE+(_Jz-_JA|0)|0;if(_JG>0){if(_JG>_JF){if(_JG<=(_JF+1|0)){if(!E(B(_IW(_JB))[2])){return 0;}else{return new F(function(){return _Io(_Ib,_Jz-_JA|0);});}}else{return 0;}}else{var _JH=B(_Ju(_JB,_JG));switch(B(_Jm(_JB,_JG-1|0))){case 0:return new F(function(){return _Io(_JH,_Jz-_JA|0);});break;case 1:if(!(B(_wi(_JH))&1)){return new F(function(){return _Io(_JH,_Jz-_JA|0);});}else{return new F(function(){return _Io(B(_uB(_JH,_Ib)),_Jz-_JA|0);});}break;default:return new F(function(){return _Io(B(_uB(_JH,_Ib)),_Jz-_JA|0);});}}}else{return new F(function(){return _Io(_JB,(_Jz-_JA|0)-_JG|0);});}}else{if(_JF>=_JA){var _JI=B(_Ju(_JB,(_JF+1|0)-_JA|0));switch(B(_Jm(_JB,_JF-_JA|0))){case 0:return new F(function(){return _Io(_JI,((_JF-_JE|0)+1|0)-_JA|0);});break;case 2:return new F(function(){return _Io(B(_uB(_JI,_Ib)),((_JF-_JE|0)+1|0)-_JA|0);});break;default:if(!(B(_wi(_JI))&1)){return new F(function(){return _Io(_JI,((_JF-_JE|0)+1|0)-_JA|0);});}else{return new F(function(){return _Io(B(_uB(_JI,_Ib)),((_JF-_JE|0)+1|0)-_JA|0);});}}}else{return new F(function(){return _Io(_JB, -_JE);});}}}else{var _JJ=B(_IO(_JB))-_JE|0,_JK=function(_JL){var _JM=function(_JN,_JO){if(!B(_wl(B(_cz(_JO,_JA)),_JN))){return new F(function(){return _IC(_JL-_JA|0,_JN,_JO);});}else{return new F(function(){return _IC((_JL-_JA|0)+1|0,_JN,B(_cz(_JO,1)));});}};if(_JL>=_JA){if(_JL!=_JA){return new F(function(){return _JM(_JB,new T(function(){return B(_cz(_JC,_JL-_JA|0));}));});}else{return new F(function(){return _JM(_JB,_JC);});}}else{return new F(function(){return _JM(new T(function(){return B(_cz(_JB,_JA-_JL|0));}),_JC);});}};if(_Jz>_JJ){return new F(function(){return _JK(_Jz);});}else{return new F(function(){return _JK(_JJ);});}}},_JP=new T(function(){return 0/0;}),_JQ=new T(function(){return -1/0;}),_JR=new T(function(){return 1/0;}),_JS=0,_JT=function(_JU,_JV){if(!B(_FK(_JV,_IB))){if(!B(_FK(_JU,_IB))){if(!B(_fs(_JU,_IB))){return new F(function(){return _Jy(-1021,53,_JU,_JV);});}else{return  -B(_Jy(-1021,53,B(_uL(_JU)),_JV));}}else{return E(_JS);}}else{return (!B(_FK(_JU,_IB)))?(!B(_fs(_JU,_IB)))?E(_JR):E(_JQ):E(_JP);}},_JW=function(_JX){var _JY=E(_JX);switch(_JY[0]){case 3:var _JZ=_JY[1];return (!B(_26(_JZ,_F8)))?(!B(_26(_JZ,_F7)))?E(_I8):E(_F4):E(_F0);case 5:var _K0=B(_HS(_Fa,_F9,_JY[1]));if(!_K0[0]){return E(_F0);}else{var _K1=new T(function(){var _K2=E(_K0[1]);return B(_JT(_K2[1],_K2[2]));});return function(_K3,_K4){return new F(function(){return A(_K4,[_K1]);});};}break;default:return E(_I8);}},_K5=new T(function(){return B(A(_EE,[_JW,_Dr,_En]));}),_K6=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:53:3-11"));}),_K7=[0,_6t,_6u,_3n,_K6,_6t,_6t],_K8=new T(function(){return B(_6r(_K7));}),_K9=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:62:3-10"));}),_Ka=[0,_6t,_6u,_3n,_K9,_6t,_6t],_Kb=new T(function(){return B(_6r(_Ka));}),_Kc=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:63:3-11"));}),_Kd=[0,_6t,_6u,_3n,_Kc,_6t,_6t],_Ke=new T(function(){return B(_6r(_Kd));}),_Kf=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:72:3-12"));}),_Kg=[0,_6t,_6u,_3n,_Kf,_6t,_6t],_Kh=new T(function(){return B(_6r(_Kg));}),_Ki=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:73:3-12"));}),_Kj=[0,_6t,_6u,_3n,_Ki,_6t,_6t],_Kk=new T(function(){return B(_6r(_Kj));}),_Kl=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:74:3-11"));}),_Km=[0,_6t,_6u,_3n,_Kl,_6t,_6t],_Kn=new T(function(){return B(_6r(_Km));}),_Ko=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:89:3-14"));}),_Kp=[0,_6t,_6u,_3n,_Ko,_6t,_6t],_Kq=new T(function(){return B(_6r(_Kp));}),_Kr=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:90:3-11"));}),_Ks=[0,_6t,_6u,_3n,_Kr,_6t,_6t],_Kt=new T(function(){return B(_6r(_Ks));}),_Ku=new T(function(){return B(unCStr("input[name=\'mount\']:checked"));}),_Kv="offset",_Kw="bottom",_Kx="top",_Ky=function(_Kz){while(1){var _KA=B((function(_KB){var _KC=E(_KB);if(!_KC[0]){return [0];}else{var _KD=_KC[2],_KE=E(_KC[1]);if(!E(_KE[2])[0]){return [1,_KE[1],new T(function(){return B(_Ky(_KD));})];}else{_Kz=_KD;return null;}}})(_Kz));if(_KA!=null){return _KA;}}},_KF=function(_KG,_KH){return [1,new T(function(){var _KI=B(_Ky(B(_rI(_K5,_KG))));if(!_KI[0]){return E(_Et);}else{if(!E(_KI[2])[0]){return E(_KI[1])*1.7453292519943295e-2;}else{return E(_Eu);}}}),_KH];},_KJ="rotations",_KK=new T(function(){return B(unCStr("loadPath"));}),_KL=function(_KM,_){var _KN=function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);},_KO=E(_KN)("processDump",toJSStr(_KK));return new F(function(){return _dQ(_);});},_KP=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:121:5-17"));}),_KQ=[0,_6t,_6u,_3n,_KP,_6t,_6t],_KR=new T(function(){return B(_6r(_KQ));}),_KS=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:124:5-19"));}),_KT=[0,_6t,_6u,_3n,_KS,_6t,_6t],_KU=new T(function(){return B(_6r(_KT));}),_KV=new T(function(){return B(unCStr(".txt"));}),_KW=new T(function(){return B(unCStr("download"));}),_KX=function(_KY,_KZ){var _L0=E(_KZ);if(!_L0[0]){return [0,_3n,_3n];}else{var _L1=_L0[1];if(!B(A(_KY,[_L1]))){var _L2=new T(function(){var _L3=B(_KX(_KY,_L0[2]));return [0,_L3[1],_L3[2]];});return [0,[1,_L1,new T(function(){return E(E(_L2)[1]);})],new T(function(){return E(E(_L2)[2]);})];}else{return [0,_3n,_L0];}}},_L4=function(_L5){var _L6=_L5>>>0;if(_L6>887){var _L7=u_iswspace(_L5);return (E(_L7)==0)?false:true;}else{var _L8=E(_L6);return (_L8==32)?true:(_L8-9>>>0>4)?(E(_L8)==160)?true:false:true;}},_L9=function(_La){return new F(function(){return _L4(E(_La));});},_Lb=function(_Lc,_Ld,_Le){var _Lf=function(_Lg){var _Lh=B(_Hw(_L9,_Lg));if(!_Lh[0]){return E(_Ld);}else{var _Li=new T(function(){var _Lj=B(_KX(_L9,_Lh));return [0,_Lj[1],_Lj[2]];});return new F(function(){return A(_Lc,[new T(function(){return E(E(_Li)[1]);}),new T(function(){return B(_Lf(E(_Li)[2]));})]);});}};return new F(function(){return _Lf(_Le);});},_Lk=function(_){var _Ll=B(A(_hN,[_6B,_qG,_])),_Lm=E(_Ll);if(!_Lm[0]){return new F(function(){return die(_Ex);});}else{var _Ln=B(A(_hN,[_6B,_qF,_])),_Lo=E(_Ln);if(!_Lo[0]){return new F(function(){return die(_EA);});}else{var _Lp=B(A(_hN,[_6B,_lg,_])),_Lq=E(_Lp);if(!_Lq[0]){return new F(function(){return die(_ED);});}else{var _Lr=_Lq[1],_Ls=B(A(_hN,[_6B,_KJ,_])),_Lt=E(_Ls);if(!_Lt[0]){return new F(function(){return die(_K8);});}else{var _Lu=_Lt[1],_Lv=nMV(_qo),_Lw=_Lv,_Lx=nMV(_qx),_Ly=_Lx,_Lz=B(A(_5,[_6B,_qE,_])),_LA=nMV(_Lz),_LB=_LA,_LC=nMV(_qE),_LD=_LC,_LE=B(A(_hN,[_6B,_lA,_])),_LF=E(_LE);if(!_LF[0]){return new F(function(){return die(_Kb);});}else{var _LG=E(_LF[1]),_LH=E(_N),_LI=_LH(_LG);if(!_LI){return new F(function(){return die(_Kb);});}else{var _LJ=E(_M),_LK=_LJ(_LG),_LL=_LK,_LM=B(A(_hN,[_6B,_lw,_])),_LN=function(_,_LO){var _LP=E(_LO);if(!_LP[0]){return new F(function(){return die(_Ke);});}else{var _LQ=function(_){return new F(function(){return _mw(_Ly,_Lw,_LB,_);});},_LR=B(_oj(_Lw,[0,_LL,_LG],_LQ,_)),_LS=B(_pw(_Ly,_LP[1],_LQ,_)),_LT=function(_LU,_){var _LV=String(E(_LU)),_LW=jsParseJSON(_LV);if(!_LW[0]){return _8P;}else{var _LX=B(_4e(_LW[1]));if(!_LX[0]){return _8P;}else{var _LY=_LX[1],_=wMV(_Lw,new T(function(){return E(E(_LY)[1]);})),_=wMV(_Ly,new T(function(){return E(E(_LY)[2]);}));return _8P;}}},_LZ=__createJSFunc(2,E(_LT)),_M0=(function(s,f){Haste[s] = f;}),_M1=E(_M0)("processDump",_LZ),_M2=B(A(_hN,[_6B,_Kx,_])),_M3=E(_M2);if(!_M3[0]){return new F(function(){return die(_Kh);});}else{var _M4=_M3[1],_M5=B(A(_hN,[_6B,_Kw,_])),_M6=E(_M5);if(!_M6[0]){return new F(function(){return die(_Kk);});}else{var _M7=_M6[1],_M8=B(A(_hN,[_6B,_Kv,_])),_M9=E(_M8);if(!_M9[0]){return new F(function(){return die(_Kn);});}else{var _Ma=_M9[1],_Mb=B(A(_q3,[_6B,_pU,_qD,_])),_Mc=function(_Md,_){var _Me=E(_Md),_Mf=toJSStr(_qC),_Mg=E(_q9)(_Mf),_Mh=B(A(_5,[_6B,new T(function(){var _Mi=String(_Mg);return fromJSStr(_Mi);}),_])),_=wMV(_LB,_Mh),_Mj=E(_qa)(_Mf),_Mk=new T(function(){var _Ml=String(_Mj);return fromJSStr(_Ml);}),_=wMV(_LD,_Mk),_Mm=B(A(_hN,[_6B,_qB,_])),_Mn=E(_Mm);if(!_Mn[0]){return new F(function(){return die(_KR);});}else{var _Mo=toJSStr(E(_KW)),_Mp=E(_9t),_Mq=_Mp(E(_Mn[1]),_Mo,toJSStr(B(_16(_Mk,_qA)))),_Mr=B(A(_hN,[_6B,_ld,_])),_Ms=E(_Mr);if(!_Ms[0]){return new F(function(){return die(_KU);});}else{var _Mt=_Mp(E(_Ms[1]),_Mo,toJSStr(B(_16(_Mk,_KV))));return new F(function(){return _mw(_Ly,_Lw,_LB,_);});}}},_Mu=B(A(_c2,[_6C,_S,_o,_Lm[1],_b4,_Mc,_])),_Mv=B(A(_c2,[_6C,_S,_o,_Lo[1],_b4,_KL,_])),_Mw=function(_){var _Mx=B(A(_hN,[_6B,_lg,_])),_My=E(_Mx);if(!_My[0]){return new F(function(){return die(_Kq);});}else{var _Mz=B(A(_hN,[_6B,_KJ,_])),_MA=E(_Mz);if(!_MA[0]){return new F(function(){return die(_Kt);});}else{var _MB=B(A(_m0,[_S,_6B,_My[1],_lf,_])),_MC=rMV(_Ly),_MD=E(_MC),_=wMV(_Ly,[0,_MD[1],_MD[2],_MB,_MD[4],_MD[5],_MD[6],_MD[7],_MD[8]]),_ME=B(A(_m0,[_S,_6B,_MA[1],_lf,_])),_MF=rMV(_Ly),_MG=E(_MF),_=wMV(_Ly,[0,_MG[1],_MG[2],_MG[3],_MG[4],_MG[5],_MG[6],_MG[7],new T(function(){return B(_Lb(_KF,_3n,_ME));})]),_MH=B(A(_hN,[_6B,_Kx,_])),_MI=B(A(_m0,[_S,_6B,new T(function(){return B(_qd(_MH));}),_lf,_])),_MJ=B(A(_hN,[_6B,_Kw,_])),_MK=B(A(_m0,[_S,_6B,new T(function(){return B(_qd(_MJ));}),_lf,_])),_ML=B(A(_hN,[_6B,_Kv,_])),_MM=B(A(_m0,[_S,_6B,new T(function(){return B(_qd(_ML));}),_lf,_])),_MN=B(A(_q3,[_6B,_pU,_Ku,_])),_MO=E(_MN);if(!_MO[0]){return new F(function(){return _nI(_);});}else{if(!E(_MO[2])[0]){var _MP=B(A(_m0,[_S,_6B,_MO[1],_lf,_])),_MQ=rMV(_Ly),_MR=E(_MQ),_=wMV(_Ly,[0,_MR[1],_MR[2],_MR[3],new T(function(){var _MS=B(_Ky(B(_rI(_K5,_MI))));if(!_MS[0]){return E(_Et);}else{if(!E(_MS[2])[0]){return E(_MS[1]);}else{return E(_Eu);}}}),new T(function(){var _MT=B(_Ky(B(_rI(_K5,_MK))));if(!_MT[0]){return E(_Et);}else{if(!E(_MT[2])[0]){return E(_MT[1]);}else{return E(_Eu);}}}),new T(function(){var _MU=B(_Ky(B(_rI(_K5,_MM))));if(!_MU[0]){return E(_Et);}else{if(!E(_MU[2])[0]){return E(_MU[1]);}else{return E(_Eu);}}}),new T(function(){var _MV=B(_Ky(B(_rI(_Es,_MP))));if(!_MV[0]){return E(_qz);}else{if(!E(_MV[2])[0]){return E(_MV[1]);}else{return E(_qI);}}}),_MR[8]]);return new F(function(){return _mw(_Ly,_Lw,_LB,_);});}else{return new F(function(){return _nI(_);});}}}}},_MW=function(_MX,_){return new F(function(){return _Mw(_);});},_MY=function(_MZ,_){while(1){var _N0=E(_MZ);if(!_N0[0]){var _N1=B(A(_c2,[_6C,_S,_o,_Lr,_b4,_MW,_])),_N2=B(A(_c2,[_6C,_S,_o,_Lu,_b4,_MW,_])),_N3=B(A(_c2,[_6C,_S,_o,_M4,_b4,_MW,_])),_N4=B(A(_c2,[_6C,_S,_o,_M7,_b4,_MW,_])),_N5=B(A(_c2,[_6C,_S,_o,_Ma,_b4,_MW,_]));return _a;}else{var _N6=B(A(_c2,[_6C,_S,_o,_N0[1],_b4,_MW,_]));_MZ=_N0[2];continue;}}},_N7=B(_MY(_Mb,_)),_N8=B(A(_c2,[_6C,_S,_L,_Lr,_nJ,_MW,_])),_N9=B(A(_c2,[_6C,_S,_L,_Lu,_nJ,_MW,_])),_Na=B(A(_c2,[_6C,_S,_L,_M4,_nJ,_MW,_])),_Nb=B(A(_c2,[_6C,_S,_L,_M7,_nJ,_MW,_])),_Nc=B(A(_c2,[_6C,_S,_L,_Ma,_nJ,_MW,_]));return new F(function(){return _mw(_Ly,_Lw,_LB,_);});}}}}},_Nd=E(_LM);if(!_Nd[0]){return new F(function(){return _LN(_,_6t);});}else{var _Ne=E(_Nd[1]),_Nf=_LH(_Ne);if(!_Nf){return new F(function(){return _LN(_,_6t);});}else{var _Ng=_LJ(_Ne);return new F(function(){return _LN(_,[1,[0,_Ng,_Ne]]);});}}}}}}}}},_Nh=function(_){return new F(function(){return _Lk(_);});};
var hasteMain = function() {B(A(_Nh, [0]));};window.onload = hasteMain;