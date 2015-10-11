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

var _0="src",_1=(function(e,p,v){e[p] = v;}),_2=function(_3){return E(E(_3)[2]);},_4=(function(t){return document.createElement(t);}),_5=function(_6,_7){return new F(function(){return A(_2,[_6,function(_){var _8=E(_4)("img"),_9=E(_1)(_8,E(_0),toJSStr(E(_7)));return _8;}]);});},_a=0,_b=function(_){return _a;},_c=function(_d,_e,_){return new F(function(){return _b(_);});},_f="scroll",_g="submit",_h="blur",_i="focus",_j="change",_k="unload",_l="load",_m=function(_n){switch(E(_n)){case 0:return E(_l);case 1:return E(_k);case 2:return E(_j);case 3:return E(_i);case 4:return E(_h);case 5:return E(_g);default:return E(_f);}},_o=[0,_m,_c],_p="metaKey",_q="shiftKey",_r="altKey",_s="ctrlKey",_t="keyCode",_u=function(_v,_){var _w=_v[E(_t)],_x=_v[E(_s)],_y=_v[E(_r)],_z=_v[E(_q)],_A=_v[E(_p)];return new T(function(){var _B=Number(_w),_C=jsTrunc(_B);return [0,_C,E(_x),E(_y),E(_z),E(_A)];});},_D=function(_E,_F,_){return new F(function(){return _u(E(_F),_);});},_G="keydown",_H="keyup",_I="keypress",_J=function(_K){switch(E(_K)){case 0:return E(_I);case 1:return E(_H);default:return E(_G);}},_L=[0,_J,_D],_M=(function(e){return e.getContext('2d');}),_N=(function(e){return !!e.getContext;}),_O=function(_P,_){return [1,_P];},_Q=function(_R){return E(_R);},_S=[0,_Q,_O],_T=function(_U){return E(E(_U)[1]);},_V=function(_W,_X){return (!B(A(_T,[_Y,_W,_X])))?true:false;},_Z=function(_10,_11){var _12=strEq(E(_10),E(_11));return (E(_12)==0)?false:true;},_13=function(_14,_15){return new F(function(){return _Z(_14,_15);});},_Y=new T(function(){return [0,_13,_V];}),_16=function(_17,_18){var _19=E(_17);return (_19[0]==0)?E(_18):[1,_19[1],new T(function(){return B(_16(_19[2],_18));})];},_1a=function(_1b,_1c){var _1d=jsShowI(_1b);return new F(function(){return _16(fromJSStr(_1d),_1c);});},_1e=41,_1f=40,_1g=function(_1h,_1i,_1j){if(_1i>=0){return new F(function(){return _1a(_1i,_1j);});}else{if(_1h<=6){return new F(function(){return _1a(_1i,_1j);});}else{return [1,_1f,new T(function(){var _1k=jsShowI(_1i);return B(_16(fromJSStr(_1k),[1,_1e,_1j]));})];}}},_1l=[0],_1m=function(_1n,_1o){var _1p=new T(function(){return B(_1g(0,_1o,_1l));});if(_1o>=0){var _1q=function(_1r,_1s){var _1t=function(_1u){var _1v=E(_1s);if(!_1v[0]){return [0,new T(function(){var _1w=new T(function(){var _1x=new T(function(){return B(unAppCStr(", length=",new T(function(){return B(_1g(0,_1o-_1r|0,_1l));})));},1);return B(_16(_1p,_1x));});return B(unAppCStr("index too large, index=",_1w));})];}else{return new F(function(){return _1q(_1r-1|0,_1v[2]);});}};if(!E(_1r)){var _1y=E(_1s);if(!_1y[0]){return new F(function(){return _1t(_);});}else{return [1,_1y[1]];}}else{return new F(function(){return _1t(_);});}};return new F(function(){return _1q(_1o,_1n);});}else{return [0,new T(function(){return B(unAppCStr("index must not be negative, index=",_1p));})];}},_1z=[1,_1l],_1A=function(_1B){var _1C=E(_1B);if(!_1C[0]){return E(_1z);}else{var _1D=E(_1C[1]);if(_1D[0]==3){var _1E=E(_1D[1]);if(!_1E[0]){return [0];}else{var _1F=E(_1E[1]);if(!_1F[0]){var _1G=B(_1m(_1E,1));if(!_1G[0]){return [0];}else{var _1H=E(_1G[1]);if(!_1H[0]){var _1I=B(_1A(_1C[2]));return (_1I[0]==0)?[0]:[1,[1,[0,_1F[1],_1H[1]],_1I[1]]];}else{return [0];}}}else{return [0];}}}else{return [0];}}},_1J=function(_1K){var _1L=E(_1K);if(_1L[0]==3){var _1M=B(_1A(_1L[1]));if(!_1M[0]){return [0];}else{var _1N=E(_1M[1]);if(!_1N[0]){return [0];}else{var _1O=B(_1m(_1N,1));if(!_1O[0]){return [0];}else{var _1P=B(_1m(_1N,2));if(!_1P[0]){return [0];}else{var _1Q=B(_1m(_1N,3));return (_1Q[0]==0)?[0]:[1,[0,_1N[1],_1O[1],_1P[1],_1Q[1]]];}}}}}else{return [0];}},_1R="box",_1S="mouse",_1T="corner",_1U="Dragging",_1V=[0],_1W=[1,_1V],_1X="Free",_1Y="state",_1Z=1,_20=[1,_1Z],_21=0,_22=[1,_21],_23=3,_24=[1,_23],_25=2,_26=[1,_25],_27=new T(function(){return B(unCStr("SW"));}),_28=new T(function(){return B(unCStr("SE"));}),_29=new T(function(){return B(unCStr("NW"));}),_2a=new T(function(){return B(unCStr("NE"));}),_2b=function(_2c,_2d){while(1){var _2e=E(_2c);if(!_2e[0]){return (E(_2d)[0]==0)?true:false;}else{var _2f=E(_2d);if(!_2f[0]){return false;}else{if(E(_2e[1])!=E(_2f[1])){return false;}else{_2c=_2e[2];_2d=_2f[2];continue;}}}}},_2g=function(_2h){var _2i=E(_2h);if(_2i[0]==1){var _2j=fromJSStr(_2i[1]);return (!B(_2b(_2j,_2a)))?(!B(_2b(_2j,_29)))?(!B(_2b(_2j,_28)))?(!B(_2b(_2j,_27)))?[0]:E(_26):E(_24):E(_22):E(_20);}else{return [0];}},_2k=function(_2l,_2m,_2n){while(1){var _2o=E(_2n);if(!_2o[0]){return [0];}else{var _2p=E(_2o[1]);if(!B(A(_T,[_2l,_2m,_2p[1]]))){_2n=_2o[2];continue;}else{return [1,_2p[2]];}}}},_2q=function(_2r){var _2s=E(_2r);if(_2s[0]==4){var _2t=_2s[1],_2u=B(_2k(_Y,_1Y,_2t));if(!_2u[0]){return [0];}else{var _2v=E(_2u[1]);if(_2v[0]==1){var _2w=_2v[1],_2x=strEq(_2w,E(_1X));if(!E(_2x)){var _2y=strEq(_2w,E(_1U));if(!E(_2y)){return [0];}else{var _2z=B(_2k(_Y,_1T,_2t));if(!_2z[0]){return [0];}else{var _2A=B(_2g(_2z[1]));return (_2A[0]==0)?[0]:[1,[1,_2A[1]]];}}}else{return E(_1W);}}else{return [0];}}}else{return [0];}},_2B=function(_2C){var _2D=E(_2C);if(_2D[0]==4){var _2E=_2D[1],_2F=B(_2k(_Y,_1S,_2E));if(!_2F[0]){return [0];}else{var _2G=B(_2q(_2F[1]));if(!_2G[0]){return [0];}else{var _2H=B(_2k(_Y,_1R,_2E));if(!_2H[0]){return [0];}else{var _2I=B(_1J(_2H[1]));return (_2I[0]==0)?[0]:[1,[0,_2G[1],_2I[1]]];}}}}else{return [0];}},_2J=function(_2K){return [0,E(_2K)];},_2L=function(_2M){var _2N=E(_2M);return (_2N[0]==0)?[1,_2N[1]]:[0];},_2O=[0,_2J,_2L],_2P=1,_2Q=[1,_2P],_2R=0,_2S=[1,_2R],_2T=new T(function(){return B(unCStr("Top"));}),_2U=new T(function(){return B(unCStr("Bottom"));}),_2V=function(_2W){var _2X=E(_2W);if(_2X[0]==1){var _2Y=fromJSStr(_2X[1]);return (!B(_2b(_2Y,_2U)))?(!B(_2b(_2Y,_2T)))?[0]:E(_2S):E(_2Q);}else{return [0];}},_2Z=1,_30=[1,_2Z],_31=0,_32=[1,_31],_33=new T(function(){return B(unCStr("Free"));}),_34=new T(function(){return B(unCStr("Dragging"));}),_35=function(_36){var _37=E(_36);if(_37[0]==1){var _38=fromJSStr(_37[1]);return (!B(_2b(_38,_34)))?(!B(_2b(_38,_33)))?[0]:E(_32):E(_30);}else{return [0];}},_39="title",_3a="points",_3b=function(_3c){var _3d=E(_3c);if(_3d[0]==4){var _3e=_3d[1],_3f=B(_2k(_Y,_3a,_3e));if(!_3f[0]){return [0];}else{var _3g=E(_3f[1]);if(_3g[0]==3){var _3h=E(_3g[1]);if(!_3h[0]){return [0];}else{var _3i=E(_3h[1]);if(_3i[0]==3){var _3j=E(_3i[1]);if(!_3j[0]){return [0];}else{var _3k=E(_3j[1]);if(!_3k[0]){var _3l=B(_1m(_3j,1));if(!_3l[0]){return [0];}else{var _3m=E(_3l[1]);if(!_3m[0]){var _3n=B(_1m(_3h,1));if(!_3n[0]){return [0];}else{var _3o=E(_3n[1]);if(_3o[0]==3){var _3p=E(_3o[1]);if(!_3p[0]){return [0];}else{var _3q=E(_3p[1]);if(!_3q[0]){var _3r=B(_1m(_3p,1));if(!_3r[0]){return [0];}else{var _3s=E(_3r[1]);if(!_3s[0]){var _3t=B(_2k(_Y,_39,_3e));if(!_3t[0]){return [0];}else{var _3u=E(_3t[1]);return (_3u[0]==1)?[1,[0,[0,_3k[1],_3m[1]],[0,_3q[1],_3s[1]],new T(function(){return fromJSStr(_3u[1]);})]]:[0];}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}},_3v=function(_3w){var _3x=new T(function(){var _3y=E(E(_3w)[2]);return [3,[1,new T(function(){return B(_2J(_3y[1]));}),[1,new T(function(){return B(_2J(_3y[2]));}),_1l]]];}),_3z=new T(function(){var _3A=E(E(_3w)[1]);return [3,[1,new T(function(){return B(_2J(_3A[1]));}),[1,new T(function(){return B(_2J(_3A[2]));}),_1l]]];});return [1,[0,_39,new T(function(){return [1,toJSStr(E(E(_3w)[3]))];})],[1,[0,_3a,[3,[1,_3z,[1,_3x,_1l]]]],_1l]];},_3B=function(_3C){return [4,E(B(_3v(_3C)))];},_3D=[0,_3B,_3b],_3E=[1,_1l],_3F=function(_3G){return E(E(_3G)[2]);},_3H=function(_3I,_3J){var _3K=E(_3J);if(_3K[0]==3){var _3L=new T(function(){return B(_3F(_3I));}),_3M=function(_3N){var _3O=E(_3N);if(!_3O[0]){return E(_3E);}else{var _3P=B(A(_3L,[_3O[1]]));if(!_3P[0]){return [0];}else{var _3Q=B(_3M(_3O[2]));return (_3Q[0]==0)?[0]:[1,[1,_3P[1],_3Q[1]]];}}};return new F(function(){return _3M(_3K[1]);});}else{return [0];}},_3R="rotations",_3S=0.1,_3T="step",_3U="choice",_3V="offset",_3W="bottom",_3X="top",_3Y="scans",_3Z="mouse",_40=function(_41){var _42=E(_41);if(_42[0]==4){var _43=_42[1],_44=B(_2k(_Y,_3Z,_43));if(!_44[0]){return [0];}else{var _45=B(_35(_44[1]));if(!_45[0]){return [0];}else{var _46=_45[1],_47=B(_2k(_Y,_3Y,_43));if(!_47[0]){return [0];}else{var _48=B(_3H(_3D,_47[1]));if(!_48[0]){return [0];}else{var _49=_48[1],_4a=B(_2k(_Y,_3X,_43));if(!_4a[0]){return [0];}else{var _4b=E(_4a[1]);if(!_4b[0]){var _4c=_4b[1],_4d=B(_2k(_Y,_3W,_43));if(!_4d[0]){return [0];}else{var _4e=E(_4d[1]);if(!_4e[0]){var _4f=_4e[1],_4g=B(_2k(_Y,_3V,_43));if(!_4g[0]){return [0];}else{var _4h=E(_4g[1]);if(!_4h[0]){var _4i=_4h[1],_4j=B(_2k(_Y,_3U,_43));if(!_4j[0]){return [0];}else{var _4k=B(_2V(_4j[1]));if(!_4k[0]){return [0];}else{var _4l=_4k[1],_4m=B(_2k(_Y,_3T,_43));if(!_4m[0]){var _4n=B(_2k(_Y,_3R,_43));if(!_4n[0]){return [0];}else{var _4o=B(_3H(_2O,_4n[1]));return (_4o[0]==0)?[0]:[1,[0,_46,_49,_4c,_4f,_4i,_4l,_3S,_4o[1]]];}}else{var _4p=E(_4m[1]);if(!_4p[0]){var _4q=B(_2k(_Y,_3R,_43));if(!_4q[0]){return [0];}else{var _4r=B(_3H(_2O,_4q[1]));return (_4r[0]==0)?[0]:[1,[0,_46,_49,_4c,_4f,_4i,_4l,_4p[1],_4r[1]]];}}else{return [0];}}}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}}}}}else{return [0];}},_4s="scans",_4t="calib",_4u=function(_4v){var _4w=E(_4v);if(_4w[0]==4){var _4x=_4w[1],_4y=B(_2k(_Y,_4t,_4x));if(!_4y[0]){return [0];}else{var _4z=B(_2B(_4y[1]));if(!_4z[0]){return [0];}else{var _4A=B(_2k(_Y,_4s,_4x));if(!_4A[0]){return [0];}else{var _4B=B(_40(_4A[1]));return (_4B[0]==0)?[0]:[1,[0,_4z[1],_4B[1]]];}}}}else{return [0];}},_4C=function(_4D,_4E,_){var _4F=B(A(_4D,[_])),_4G=B(A(_4E,[_]));return _4F;},_4H=function(_4I,_4J,_){var _4K=B(A(_4I,[_])),_4L=B(A(_4J,[_]));return new T(function(){return B(A(_4K,[_4L]));});},_4M=function(_4N,_4O,_){var _4P=B(A(_4O,[_]));return _4N;},_4Q=function(_4R,_4S,_){var _4T=B(A(_4S,[_]));return new T(function(){return B(A(_4R,[_4T]));});},_4U=[0,_4Q,_4M],_4V=function(_4W,_){return _4W;},_4X=function(_4Y,_4Z,_){var _50=B(A(_4Y,[_]));return new F(function(){return A(_4Z,[_]);});},_51=[0,_4U,_4V,_4H,_4X,_4C],_52=function(_53,_54,_){var _55=B(A(_53,[_]));return new F(function(){return A(_54,[_55,_]);});},_56=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_57=new T(function(){return B(unCStr("base"));}),_58=new T(function(){return B(unCStr("IOException"));}),_59=new T(function(){var _5a=hs_wordToWord64(4053623282),_5b=hs_wordToWord64(3693590983);return [0,_5a,_5b,[0,_5a,_5b,_57,_56,_58],_1l,_1l];}),_5c=function(_5d){return E(_59);},_5e=function(_5f){return E(E(_5f)[1]);},_5g=function(_5h,_5i,_5j){var _5k=B(A(_5h,[_])),_5l=B(A(_5i,[_])),_5m=hs_eqWord64(_5k[1],_5l[1]);if(!_5m){return [0];}else{var _5n=hs_eqWord64(_5k[2],_5l[2]);return (!_5n)?[0]:[1,_5j];}},_5o=function(_5p){var _5q=E(_5p);return new F(function(){return _5g(B(_5e(_5q[1])),_5c,_5q[2]);});},_5r=new T(function(){return B(unCStr(": "));}),_5s=new T(function(){return B(unCStr(")"));}),_5t=new T(function(){return B(unCStr(" ("));}),_5u=new T(function(){return B(unCStr("interrupted"));}),_5v=new T(function(){return B(unCStr("system error"));}),_5w=new T(function(){return B(unCStr("unsatisified constraints"));}),_5x=new T(function(){return B(unCStr("user error"));}),_5y=new T(function(){return B(unCStr("permission denied"));}),_5z=new T(function(){return B(unCStr("illegal operation"));}),_5A=new T(function(){return B(unCStr("end of file"));}),_5B=new T(function(){return B(unCStr("resource exhausted"));}),_5C=new T(function(){return B(unCStr("resource busy"));}),_5D=new T(function(){return B(unCStr("does not exist"));}),_5E=new T(function(){return B(unCStr("already exists"));}),_5F=new T(function(){return B(unCStr("resource vanished"));}),_5G=new T(function(){return B(unCStr("timeout"));}),_5H=new T(function(){return B(unCStr("unsupported operation"));}),_5I=new T(function(){return B(unCStr("hardware fault"));}),_5J=new T(function(){return B(unCStr("inappropriate type"));}),_5K=new T(function(){return B(unCStr("invalid argument"));}),_5L=new T(function(){return B(unCStr("failed"));}),_5M=new T(function(){return B(unCStr("protocol error"));}),_5N=function(_5O,_5P){switch(E(_5O)){case 0:return new F(function(){return _16(_5E,_5P);});break;case 1:return new F(function(){return _16(_5D,_5P);});break;case 2:return new F(function(){return _16(_5C,_5P);});break;case 3:return new F(function(){return _16(_5B,_5P);});break;case 4:return new F(function(){return _16(_5A,_5P);});break;case 5:return new F(function(){return _16(_5z,_5P);});break;case 6:return new F(function(){return _16(_5y,_5P);});break;case 7:return new F(function(){return _16(_5x,_5P);});break;case 8:return new F(function(){return _16(_5w,_5P);});break;case 9:return new F(function(){return _16(_5v,_5P);});break;case 10:return new F(function(){return _16(_5M,_5P);});break;case 11:return new F(function(){return _16(_5L,_5P);});break;case 12:return new F(function(){return _16(_5K,_5P);});break;case 13:return new F(function(){return _16(_5J,_5P);});break;case 14:return new F(function(){return _16(_5I,_5P);});break;case 15:return new F(function(){return _16(_5H,_5P);});break;case 16:return new F(function(){return _16(_5G,_5P);});break;case 17:return new F(function(){return _16(_5F,_5P);});break;default:return new F(function(){return _16(_5u,_5P);});}},_5Q=new T(function(){return B(unCStr("}"));}),_5R=new T(function(){return B(unCStr("{handle: "));}),_5S=function(_5T,_5U,_5V,_5W,_5X,_5Y){var _5Z=new T(function(){var _60=new T(function(){var _61=new T(function(){var _62=E(_5W);if(!_62[0]){return E(_5Y);}else{var _63=new T(function(){return B(_16(_62,new T(function(){return B(_16(_5s,_5Y));},1)));},1);return B(_16(_5t,_63));}},1);return B(_5N(_5U,_61));}),_64=E(_5V);if(!_64[0]){return E(_60);}else{return B(_16(_64,new T(function(){return B(_16(_5r,_60));},1)));}}),_65=E(_5X);if(!_65[0]){var _66=E(_5T);if(!_66[0]){return E(_5Z);}else{var _67=E(_66[1]);if(!_67[0]){var _68=new T(function(){var _69=new T(function(){return B(_16(_5Q,new T(function(){return B(_16(_5r,_5Z));},1)));},1);return B(_16(_67[1],_69));},1);return new F(function(){return _16(_5R,_68);});}else{var _6a=new T(function(){var _6b=new T(function(){return B(_16(_5Q,new T(function(){return B(_16(_5r,_5Z));},1)));},1);return B(_16(_67[1],_6b));},1);return new F(function(){return _16(_5R,_6a);});}}}else{return new F(function(){return _16(_65[1],new T(function(){return B(_16(_5r,_5Z));},1));});}},_6c=function(_6d){var _6e=E(_6d);return new F(function(){return _5S(_6e[1],_6e[2],_6e[3],_6e[4],_6e[6],_1l);});},_6f=function(_6g,_6h,_6i){var _6j=E(_6h);return new F(function(){return _5S(_6j[1],_6j[2],_6j[3],_6j[4],_6j[6],_6i);});},_6k=function(_6l,_6m){var _6n=E(_6l);return new F(function(){return _5S(_6n[1],_6n[2],_6n[3],_6n[4],_6n[6],_6m);});},_6o=44,_6p=93,_6q=91,_6r=function(_6s,_6t,_6u){var _6v=E(_6t);if(!_6v[0]){return new F(function(){return unAppCStr("[]",_6u);});}else{var _6w=new T(function(){var _6x=new T(function(){var _6y=function(_6z){var _6A=E(_6z);if(!_6A[0]){return [1,_6p,_6u];}else{var _6B=new T(function(){return B(A(_6s,[_6A[1],new T(function(){return B(_6y(_6A[2]));})]));});return [1,_6o,_6B];}};return B(_6y(_6v[2]));});return B(A(_6s,[_6v[1],_6x]));});return [1,_6q,_6w];}},_6C=function(_6D,_6E){return new F(function(){return _6r(_6k,_6D,_6E);});},_6F=[0,_6f,_6c,_6C],_6G=new T(function(){return [0,_5c,_6F,_6H,_5o,_6c];}),_6H=function(_6I){return [0,_6G,_6I];},_6J=[0],_6K=7,_6L=function(_6M){return [0,_6J,_6K,_1l,_6M,_6J,_6J];},_6N=function(_6O,_){var _6P=new T(function(){return B(_6H(new T(function(){return B(_6L(_6O));})));});return new F(function(){return die(_6P);});},_6Q=[0,_51,_52,_4X,_4V,_6N],_6R=[0,_6Q,_Q],_6S=[0,_6R,_4V],_6T=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6U=new T(function(){return B(unCStr("base"));}),_6V=new T(function(){return B(unCStr("PatternMatchFail"));}),_6W=new T(function(){var _6X=hs_wordToWord64(18445595),_6Y=hs_wordToWord64(52003073);return [0,_6X,_6Y,[0,_6X,_6Y,_6U,_6T,_6V],_1l,_1l];}),_6Z=function(_70){return E(_6W);},_71=function(_72){var _73=E(_72);return new F(function(){return _5g(B(_5e(_73[1])),_6Z,_73[2]);});},_74=function(_75){return E(E(_75)[1]);},_76=function(_77){return [0,_78,_77];},_79=function(_7a,_7b){return new F(function(){return _16(E(_7a)[1],_7b);});},_7c=function(_7d,_7e){return new F(function(){return _6r(_79,_7d,_7e);});},_7f=function(_7g,_7h,_7i){return new F(function(){return _16(E(_7h)[1],_7i);});},_7j=[0,_7f,_74,_7c],_78=new T(function(){return [0,_6Z,_7j,_76,_71,_74];}),_7k=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_7l=function(_7m){return E(E(_7m)[3]);},_7n=function(_7o,_7p){return new F(function(){return die(new T(function(){return B(A(_7l,[_7p,_7o]));}));});},_7q=function(_7r,_7s){return new F(function(){return _7n(_7r,_7s);});},_7t=function(_7u,_7v){var _7w=E(_7v);if(!_7w[0]){return [0,_1l,_1l];}else{var _7x=_7w[1];if(!B(A(_7u,[_7x]))){return [0,_1l,_7w];}else{var _7y=new T(function(){var _7z=B(_7t(_7u,_7w[2]));return [0,_7z[1],_7z[2]];});return [0,[1,_7x,new T(function(){return E(E(_7y)[1]);})],new T(function(){return E(E(_7y)[2]);})];}}},_7A=32,_7B=new T(function(){return B(unCStr("\n"));}),_7C=function(_7D){return (E(_7D)==124)?false:true;},_7E=function(_7F,_7G){var _7H=B(_7t(_7C,B(unCStr(_7F)))),_7I=_7H[1],_7J=function(_7K,_7L){var _7M=new T(function(){var _7N=new T(function(){return B(_16(_7G,new T(function(){return B(_16(_7L,_7B));},1)));});return B(unAppCStr(": ",_7N));},1);return new F(function(){return _16(_7K,_7M);});},_7O=E(_7H[2]);if(!_7O[0]){return new F(function(){return _7J(_7I,_1l);});}else{if(E(_7O[1])==124){return new F(function(){return _7J(_7I,[1,_7A,_7O[2]]);});}else{return new F(function(){return _7J(_7I,_1l);});}}},_7P=function(_7Q){return new F(function(){return _7q([0,new T(function(){return B(_7E(_7Q,_7k));})],_78);});},_7R=new T(function(){return B(_7P("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_7S=function(_7T,_7U){while(1){var _7V=B((function(_7W,_7X){var _7Y=E(_7W);switch(_7Y[0]){case 0:var _7Z=E(_7X);if(!_7Z[0]){return [0];}else{_7T=B(A(_7Y[1],[_7Z[1]]));_7U=_7Z[2];return null;}break;case 1:var _80=B(A(_7Y[1],[_7X])),_81=_7X;_7T=_80;_7U=_81;return null;case 2:return [0];case 3:return [1,[0,_7Y[1],_7X],new T(function(){return B(_7S(_7Y[2],_7X));})];default:return E(_7Y[1]);}})(_7T,_7U));if(_7V!=null){return _7V;}}},_82=function(_83,_84){var _85=function(_86){var _87=E(_84);if(_87[0]==3){return [3,_87[1],new T(function(){return B(_82(_83,_87[2]));})];}else{var _88=E(_83);if(_88[0]==2){return E(_87);}else{var _89=E(_87);if(_89[0]==2){return E(_88);}else{var _8a=function(_8b){var _8c=E(_89);if(_8c[0]==4){return [1,function(_8d){return [4,new T(function(){return B(_16(B(_7S(_88,_8d)),_8c[1]));})];}];}else{var _8e=E(_88);if(_8e[0]==1){var _8f=_8e[1],_8g=E(_8c);if(!_8g[0]){return [1,function(_8h){return new F(function(){return _82(B(A(_8f,[_8h])),_8g);});}];}else{return [1,function(_8i){return new F(function(){return _82(B(A(_8f,[_8i])),new T(function(){return B(A(_8g[1],[_8i]));}));});}];}}else{var _8j=E(_8c);if(!_8j[0]){return E(_7R);}else{return [1,function(_8k){return new F(function(){return _82(_8e,new T(function(){return B(A(_8j[1],[_8k]));}));});}];}}}},_8l=E(_88);switch(_8l[0]){case 1:var _8m=E(_89);if(_8m[0]==4){return [1,function(_8n){return [4,new T(function(){return B(_16(B(_7S(B(A(_8l[1],[_8n])),_8n)),_8m[1]));})];}];}else{return new F(function(){return _8a(_);});}break;case 4:var _8o=_8l[1],_8p=E(_89);switch(_8p[0]){case 0:return [1,function(_8q){return [4,new T(function(){return B(_16(_8o,new T(function(){return B(_7S(_8p,_8q));},1)));})];}];case 1:return [1,function(_8r){return [4,new T(function(){return B(_16(_8o,new T(function(){return B(_7S(B(A(_8p[1],[_8r])),_8r));},1)));})];}];default:return [4,new T(function(){return B(_16(_8o,_8p[1]));})];}break;default:return new F(function(){return _8a(_);});}}}}},_8s=E(_83);switch(_8s[0]){case 0:var _8t=E(_84);if(!_8t[0]){return [0,function(_8u){return new F(function(){return _82(B(A(_8s[1],[_8u])),new T(function(){return B(A(_8t[1],[_8u]));}));});}];}else{return new F(function(){return _85(_);});}break;case 3:return [3,_8s[1],new T(function(){return B(_82(_8s[2],_84));})];default:return new F(function(){return _85(_);});}},_8v=new T(function(){return B(unCStr("("));}),_8w=new T(function(){return B(unCStr(")"));}),_8x=function(_8y,_8z){return E(_8y)!=E(_8z);},_8A=function(_8B,_8C){return E(_8B)==E(_8C);},_8D=[0,_8A,_8x],_8E=function(_8F,_8G){while(1){var _8H=E(_8F);if(!_8H[0]){return (E(_8G)[0]==0)?true:false;}else{var _8I=E(_8G);if(!_8I[0]){return false;}else{if(E(_8H[1])!=E(_8I[1])){return false;}else{_8F=_8H[2];_8G=_8I[2];continue;}}}}},_8J=function(_8K,_8L){return (!B(_8E(_8K,_8L)))?true:false;},_8M=[0,_8E,_8J],_8N=function(_8O,_8P){var _8Q=E(_8O);switch(_8Q[0]){case 0:return [0,function(_8R){return new F(function(){return _8N(B(A(_8Q[1],[_8R])),_8P);});}];case 1:return [1,function(_8S){return new F(function(){return _8N(B(A(_8Q[1],[_8S])),_8P);});}];case 2:return [2];case 3:return new F(function(){return _82(B(A(_8P,[_8Q[1]])),new T(function(){return B(_8N(_8Q[2],_8P));}));});break;default:var _8T=function(_8U){var _8V=E(_8U);if(!_8V[0]){return [0];}else{var _8W=E(_8V[1]);return new F(function(){return _16(B(_7S(B(A(_8P,[_8W[1]])),_8W[2])),new T(function(){return B(_8T(_8V[2]));},1));});}},_8X=B(_8T(_8Q[1]));return (_8X[0]==0)?[2]:[4,_8X];}},_8Y=[2],_8Z=function(_90){return [3,_90,_8Y];},_91=function(_92,_93){var _94=E(_92);if(!_94){return new F(function(){return A(_93,[_a]);});}else{var _95=new T(function(){return B(_91(_94-1|0,_93));});return [0,function(_96){return E(_95);}];}},_97=function(_98,_99,_9a){var _9b=new T(function(){return B(A(_98,[_8Z]));}),_9c=function(_9d,_9e,_9f,_9g){while(1){var _9h=B((function(_9i,_9j,_9k,_9l){var _9m=E(_9i);switch(_9m[0]){case 0:var _9n=E(_9j);if(!_9n[0]){return new F(function(){return A(_99,[_9l]);});}else{var _9o=_9k+1|0,_9p=_9l;_9d=B(A(_9m[1],[_9n[1]]));_9e=_9n[2];_9f=_9o;_9g=_9p;return null;}break;case 1:var _9q=B(A(_9m[1],[_9j])),_9r=_9j,_9o=_9k,_9p=_9l;_9d=_9q;_9e=_9r;_9f=_9o;_9g=_9p;return null;case 2:return new F(function(){return A(_99,[_9l]);});break;case 3:var _9s=new T(function(){return B(_8N(_9m,_9l));});return new F(function(){return _91(_9k,function(_9t){return E(_9s);});});break;default:return new F(function(){return _8N(_9m,_9l);});}})(_9d,_9e,_9f,_9g));if(_9h!=null){return _9h;}}};return function(_9u){return new F(function(){return _9c(_9b,_9u,0,_9a);});};},_9v=function(_9w){return new F(function(){return A(_9w,[_1l]);});},_9x=function(_9y,_9z){var _9A=function(_9B){var _9C=E(_9B);if(!_9C[0]){return E(_9v);}else{var _9D=_9C[1];if(!B(A(_9y,[_9D]))){return E(_9v);}else{var _9E=new T(function(){return B(_9A(_9C[2]));}),_9F=function(_9G){var _9H=new T(function(){return B(A(_9E,[function(_9I){return new F(function(){return A(_9G,[[1,_9D,_9I]]);});}]));});return [0,function(_9J){return E(_9H);}];};return E(_9F);}}};return function(_9K){return new F(function(){return A(_9A,[_9K,_9z]);});};},_9L=[6],_9M=new T(function(){return B(unCStr("valDig: Bad base"));}),_9N=new T(function(){return B(err(_9M));}),_9O=function(_9P,_9Q){var _9R=function(_9S,_9T){var _9U=E(_9S);if(!_9U[0]){var _9V=new T(function(){return B(A(_9T,[_1l]));});return function(_9W){return new F(function(){return A(_9W,[_9V]);});};}else{var _9X=E(_9U[1]),_9Y=function(_9Z){var _a0=new T(function(){return B(_9R(_9U[2],function(_a1){return new F(function(){return A(_9T,[[1,_9Z,_a1]]);});}));}),_a2=function(_a3){var _a4=new T(function(){return B(A(_a0,[_a3]));});return [0,function(_a5){return E(_a4);}];};return E(_a2);};switch(E(_9P)){case 8:if(48>_9X){var _a6=new T(function(){return B(A(_9T,[_1l]));});return function(_a7){return new F(function(){return A(_a7,[_a6]);});};}else{if(_9X>55){var _a8=new T(function(){return B(A(_9T,[_1l]));});return function(_a9){return new F(function(){return A(_a9,[_a8]);});};}else{return new F(function(){return _9Y(_9X-48|0);});}}break;case 10:if(48>_9X){var _aa=new T(function(){return B(A(_9T,[_1l]));});return function(_ab){return new F(function(){return A(_ab,[_aa]);});};}else{if(_9X>57){var _ac=new T(function(){return B(A(_9T,[_1l]));});return function(_ad){return new F(function(){return A(_ad,[_ac]);});};}else{return new F(function(){return _9Y(_9X-48|0);});}}break;case 16:if(48>_9X){if(97>_9X){if(65>_9X){var _ae=new T(function(){return B(A(_9T,[_1l]));});return function(_af){return new F(function(){return A(_af,[_ae]);});};}else{if(_9X>70){var _ag=new T(function(){return B(A(_9T,[_1l]));});return function(_ah){return new F(function(){return A(_ah,[_ag]);});};}else{return new F(function(){return _9Y((_9X-65|0)+10|0);});}}}else{if(_9X>102){if(65>_9X){var _ai=new T(function(){return B(A(_9T,[_1l]));});return function(_aj){return new F(function(){return A(_aj,[_ai]);});};}else{if(_9X>70){var _ak=new T(function(){return B(A(_9T,[_1l]));});return function(_al){return new F(function(){return A(_al,[_ak]);});};}else{return new F(function(){return _9Y((_9X-65|0)+10|0);});}}}else{return new F(function(){return _9Y((_9X-97|0)+10|0);});}}}else{if(_9X>57){if(97>_9X){if(65>_9X){var _am=new T(function(){return B(A(_9T,[_1l]));});return function(_an){return new F(function(){return A(_an,[_am]);});};}else{if(_9X>70){var _ao=new T(function(){return B(A(_9T,[_1l]));});return function(_ap){return new F(function(){return A(_ap,[_ao]);});};}else{return new F(function(){return _9Y((_9X-65|0)+10|0);});}}}else{if(_9X>102){if(65>_9X){var _aq=new T(function(){return B(A(_9T,[_1l]));});return function(_ar){return new F(function(){return A(_ar,[_aq]);});};}else{if(_9X>70){var _as=new T(function(){return B(A(_9T,[_1l]));});return function(_at){return new F(function(){return A(_at,[_as]);});};}else{return new F(function(){return _9Y((_9X-65|0)+10|0);});}}}else{return new F(function(){return _9Y((_9X-97|0)+10|0);});}}}else{return new F(function(){return _9Y(_9X-48|0);});}}break;default:return E(_9N);}}},_au=function(_av){var _aw=E(_av);if(!_aw[0]){return [2];}else{return new F(function(){return A(_9Q,[_aw]);});}};return function(_ax){return new F(function(){return A(_9R,[_ax,_Q,_au]);});};},_ay=16,_az=8,_aA=function(_aB){var _aC=function(_aD){return new F(function(){return A(_aB,[[5,[0,_az,_aD]]]);});},_aE=function(_aF){return new F(function(){return A(_aB,[[5,[0,_ay,_aF]]]);});},_aG=function(_aH){switch(E(_aH)){case 79:return [1,B(_9O(_az,_aC))];case 88:return [1,B(_9O(_ay,_aE))];case 111:return [1,B(_9O(_az,_aC))];case 120:return [1,B(_9O(_ay,_aE))];default:return [2];}};return function(_aI){return (E(_aI)==48)?[0,_aG]:[2];};},_aJ=function(_aK){return [0,B(_aA(_aK))];},_aL=function(_aM){return new F(function(){return A(_aM,[_6J]);});},_aN=function(_aO){return new F(function(){return A(_aO,[_6J]);});},_aP=10,_aQ=[0,1],_aR=[0,2147483647],_aS=function(_aT,_aU){while(1){var _aV=E(_aT);if(!_aV[0]){var _aW=_aV[1],_aX=E(_aU);if(!_aX[0]){var _aY=_aX[1],_aZ=addC(_aW,_aY);if(!E(_aZ[2])){return [0,_aZ[1]];}else{_aT=[1,I_fromInt(_aW)];_aU=[1,I_fromInt(_aY)];continue;}}else{_aT=[1,I_fromInt(_aW)];_aU=_aX;continue;}}else{var _b0=E(_aU);if(!_b0[0]){_aT=_aV;_aU=[1,I_fromInt(_b0[1])];continue;}else{return [1,I_add(_aV[1],_b0[1])];}}}},_b1=new T(function(){return B(_aS(_aR,_aQ));}),_b2=function(_b3){var _b4=E(_b3);if(!_b4[0]){var _b5=E(_b4[1]);return (_b5==(-2147483648))?E(_b1):[0, -_b5];}else{return [1,I_negate(_b4[1])];}},_b6=[0,10],_b7=function(_b8,_b9){while(1){var _ba=E(_b8);if(!_ba[0]){return E(_b9);}else{var _bb=_b9+1|0;_b8=_ba[2];_b9=_bb;continue;}}},_bc=function(_bd,_be){var _bf=E(_be);return (_bf[0]==0)?[0]:[1,new T(function(){return B(A(_bd,[_bf[1]]));}),new T(function(){return B(_bc(_bd,_bf[2]));})];},_bg=function(_bh){return [0,_bh];},_bi=function(_bj){return new F(function(){return _bg(E(_bj));});},_bk=new T(function(){return B(unCStr("this should not happen"));}),_bl=new T(function(){return B(err(_bk));}),_bm=function(_bn,_bo){while(1){var _bp=E(_bn);if(!_bp[0]){var _bq=_bp[1],_br=E(_bo);if(!_br[0]){var _bs=_br[1];if(!(imul(_bq,_bs)|0)){return [0,imul(_bq,_bs)|0];}else{_bn=[1,I_fromInt(_bq)];_bo=[1,I_fromInt(_bs)];continue;}}else{_bn=[1,I_fromInt(_bq)];_bo=_br;continue;}}else{var _bt=E(_bo);if(!_bt[0]){_bn=_bp;_bo=[1,I_fromInt(_bt[1])];continue;}else{return [1,I_mul(_bp[1],_bt[1])];}}}},_bu=function(_bv,_bw){var _bx=E(_bw);if(!_bx[0]){return [0];}else{var _by=E(_bx[2]);return (_by[0]==0)?E(_bl):[1,B(_aS(B(_bm(_bx[1],_bv)),_by[1])),new T(function(){return B(_bu(_bv,_by[2]));})];}},_bz=[0,0],_bA=function(_bB,_bC,_bD){while(1){var _bE=B((function(_bF,_bG,_bH){var _bI=E(_bH);if(!_bI[0]){return E(_bz);}else{if(!E(_bI[2])[0]){return E(_bI[1]);}else{var _bJ=E(_bG);if(_bJ<=40){var _bK=_bz,_bL=_bI;while(1){var _bM=E(_bL);if(!_bM[0]){return E(_bK);}else{var _bN=B(_aS(B(_bm(_bK,_bF)),_bM[1]));_bK=_bN;_bL=_bM[2];continue;}}}else{var _bO=B(_bm(_bF,_bF));if(!(_bJ%2)){var _bP=B(_bu(_bF,_bI));_bB=_bO;_bC=quot(_bJ+1|0,2);_bD=_bP;return null;}else{var _bP=B(_bu(_bF,[1,_bz,_bI]));_bB=_bO;_bC=quot(_bJ+1|0,2);_bD=_bP;return null;}}}}})(_bB,_bC,_bD));if(_bE!=null){return _bE;}}},_bQ=function(_bR,_bS){return new F(function(){return _bA(_bR,new T(function(){return B(_b7(_bS,0));},1),B(_bc(_bi,_bS)));});},_bT=function(_bU){var _bV=new T(function(){var _bW=new T(function(){var _bX=function(_bY){return new F(function(){return A(_bU,[[1,new T(function(){return B(_bQ(_b6,_bY));})]]);});};return [1,B(_9O(_aP,_bX))];}),_bZ=function(_c0){if(E(_c0)==43){var _c1=function(_c2){return new F(function(){return A(_bU,[[1,new T(function(){return B(_bQ(_b6,_c2));})]]);});};return [1,B(_9O(_aP,_c1))];}else{return [2];}},_c3=function(_c4){if(E(_c4)==45){var _c5=function(_c6){return new F(function(){return A(_bU,[[1,new T(function(){return B(_b2(B(_bQ(_b6,_c6))));})]]);});};return [1,B(_9O(_aP,_c5))];}else{return [2];}};return B(_82(B(_82([0,_c3],[0,_bZ])),_bW));});return new F(function(){return _82([0,function(_c7){return (E(_c7)==101)?E(_bV):[2];}],[0,function(_c8){return (E(_c8)==69)?E(_bV):[2];}]);});},_c9=function(_ca){var _cb=function(_cc){return new F(function(){return A(_ca,[[1,_cc]]);});};return function(_cd){return (E(_cd)==46)?[1,B(_9O(_aP,_cb))]:[2];};},_ce=function(_cf){return [0,B(_c9(_cf))];},_cg=function(_ch){var _ci=function(_cj){var _ck=function(_cl){return [1,B(_97(_bT,_aL,function(_cm){return new F(function(){return A(_ch,[[5,[1,_cj,_cl,_cm]]]);});}))];};return [1,B(_97(_ce,_aN,_ck))];};return new F(function(){return _9O(_aP,_ci);});},_cn=function(_co){return [1,B(_cg(_co))];},_cp=function(_cq,_cr,_cs){while(1){var _ct=E(_cs);if(!_ct[0]){return false;}else{if(!B(A(_T,[_cq,_cr,_ct[1]]))){_cs=_ct[2];continue;}else{return true;}}}},_cu=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_cv=function(_cw){return new F(function(){return _cp(_8D,_cw,_cu);});},_cx=false,_cy=true,_cz=function(_cA){var _cB=new T(function(){return B(A(_cA,[_az]));}),_cC=new T(function(){return B(A(_cA,[_ay]));});return function(_cD){switch(E(_cD)){case 79:return E(_cB);case 88:return E(_cC);case 111:return E(_cB);case 120:return E(_cC);default:return [2];}};},_cE=function(_cF){return [0,B(_cz(_cF))];},_cG=function(_cH){return new F(function(){return A(_cH,[_aP]);});},_cI=function(_cJ){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_1g(9,_cJ,_1l));}))));});},_cK=function(_cL){var _cM=E(_cL);if(!_cM[0]){return E(_cM[1]);}else{return new F(function(){return I_toInt(_cM[1]);});}},_cN=function(_cO,_cP){var _cQ=E(_cO);if(!_cQ[0]){var _cR=_cQ[1],_cS=E(_cP);return (_cS[0]==0)?_cR<=_cS[1]:I_compareInt(_cS[1],_cR)>=0;}else{var _cT=_cQ[1],_cU=E(_cP);return (_cU[0]==0)?I_compareInt(_cT,_cU[1])<=0:I_compare(_cT,_cU[1])<=0;}},_cV=function(_cW){return [2];},_cX=function(_cY){var _cZ=E(_cY);if(!_cZ[0]){return E(_cV);}else{var _d0=_cZ[1],_d1=E(_cZ[2]);if(!_d1[0]){return E(_d0);}else{var _d2=new T(function(){return B(_cX(_d1));}),_d3=function(_d4){return new F(function(){return _82(B(A(_d0,[_d4])),new T(function(){return B(A(_d2,[_d4]));}));});};return E(_d3);}}},_d5=function(_d6,_d7){var _d8=function(_d9,_da,_db){var _dc=E(_d9);if(!_dc[0]){return new F(function(){return A(_db,[_d6]);});}else{var _dd=E(_da);if(!_dd[0]){return [2];}else{if(E(_dc[1])!=E(_dd[1])){return [2];}else{var _de=new T(function(){return B(_d8(_dc[2],_dd[2],_db));});return [0,function(_df){return E(_de);}];}}}};return function(_dg){return new F(function(){return _d8(_d6,_dg,_d7);});};},_dh=new T(function(){return B(unCStr("SO"));}),_di=14,_dj=function(_dk){var _dl=new T(function(){return B(A(_dk,[_di]));});return [1,B(_d5(_dh,function(_dm){return E(_dl);}))];},_dn=new T(function(){return B(unCStr("SOH"));}),_do=1,_dp=function(_dq){var _dr=new T(function(){return B(A(_dq,[_do]));});return [1,B(_d5(_dn,function(_ds){return E(_dr);}))];},_dt=function(_du){return [1,B(_97(_dp,_dj,_du))];},_dv=new T(function(){return B(unCStr("NUL"));}),_dw=0,_dx=function(_dy){var _dz=new T(function(){return B(A(_dy,[_dw]));});return [1,B(_d5(_dv,function(_dA){return E(_dz);}))];},_dB=new T(function(){return B(unCStr("STX"));}),_dC=2,_dD=function(_dE){var _dF=new T(function(){return B(A(_dE,[_dC]));});return [1,B(_d5(_dB,function(_dG){return E(_dF);}))];},_dH=new T(function(){return B(unCStr("ETX"));}),_dI=3,_dJ=function(_dK){var _dL=new T(function(){return B(A(_dK,[_dI]));});return [1,B(_d5(_dH,function(_dM){return E(_dL);}))];},_dN=new T(function(){return B(unCStr("EOT"));}),_dO=4,_dP=function(_dQ){var _dR=new T(function(){return B(A(_dQ,[_dO]));});return [1,B(_d5(_dN,function(_dS){return E(_dR);}))];},_dT=new T(function(){return B(unCStr("ENQ"));}),_dU=5,_dV=function(_dW){var _dX=new T(function(){return B(A(_dW,[_dU]));});return [1,B(_d5(_dT,function(_dY){return E(_dX);}))];},_dZ=new T(function(){return B(unCStr("ACK"));}),_e0=6,_e1=function(_e2){var _e3=new T(function(){return B(A(_e2,[_e0]));});return [1,B(_d5(_dZ,function(_e4){return E(_e3);}))];},_e5=new T(function(){return B(unCStr("BEL"));}),_e6=7,_e7=function(_e8){var _e9=new T(function(){return B(A(_e8,[_e6]));});return [1,B(_d5(_e5,function(_ea){return E(_e9);}))];},_eb=new T(function(){return B(unCStr("BS"));}),_ec=8,_ed=function(_ee){var _ef=new T(function(){return B(A(_ee,[_ec]));});return [1,B(_d5(_eb,function(_eg){return E(_ef);}))];},_eh=new T(function(){return B(unCStr("HT"));}),_ei=9,_ej=function(_ek){var _el=new T(function(){return B(A(_ek,[_ei]));});return [1,B(_d5(_eh,function(_em){return E(_el);}))];},_en=new T(function(){return B(unCStr("LF"));}),_eo=10,_ep=function(_eq){var _er=new T(function(){return B(A(_eq,[_eo]));});return [1,B(_d5(_en,function(_es){return E(_er);}))];},_et=new T(function(){return B(unCStr("VT"));}),_eu=11,_ev=function(_ew){var _ex=new T(function(){return B(A(_ew,[_eu]));});return [1,B(_d5(_et,function(_ey){return E(_ex);}))];},_ez=new T(function(){return B(unCStr("FF"));}),_eA=12,_eB=function(_eC){var _eD=new T(function(){return B(A(_eC,[_eA]));});return [1,B(_d5(_ez,function(_eE){return E(_eD);}))];},_eF=new T(function(){return B(unCStr("CR"));}),_eG=13,_eH=function(_eI){var _eJ=new T(function(){return B(A(_eI,[_eG]));});return [1,B(_d5(_eF,function(_eK){return E(_eJ);}))];},_eL=new T(function(){return B(unCStr("SI"));}),_eM=15,_eN=function(_eO){var _eP=new T(function(){return B(A(_eO,[_eM]));});return [1,B(_d5(_eL,function(_eQ){return E(_eP);}))];},_eR=new T(function(){return B(unCStr("DLE"));}),_eS=16,_eT=function(_eU){var _eV=new T(function(){return B(A(_eU,[_eS]));});return [1,B(_d5(_eR,function(_eW){return E(_eV);}))];},_eX=new T(function(){return B(unCStr("DC1"));}),_eY=17,_eZ=function(_f0){var _f1=new T(function(){return B(A(_f0,[_eY]));});return [1,B(_d5(_eX,function(_f2){return E(_f1);}))];},_f3=new T(function(){return B(unCStr("DC2"));}),_f4=18,_f5=function(_f6){var _f7=new T(function(){return B(A(_f6,[_f4]));});return [1,B(_d5(_f3,function(_f8){return E(_f7);}))];},_f9=new T(function(){return B(unCStr("DC3"));}),_fa=19,_fb=function(_fc){var _fd=new T(function(){return B(A(_fc,[_fa]));});return [1,B(_d5(_f9,function(_fe){return E(_fd);}))];},_ff=new T(function(){return B(unCStr("DC4"));}),_fg=20,_fh=function(_fi){var _fj=new T(function(){return B(A(_fi,[_fg]));});return [1,B(_d5(_ff,function(_fk){return E(_fj);}))];},_fl=new T(function(){return B(unCStr("NAK"));}),_fm=21,_fn=function(_fo){var _fp=new T(function(){return B(A(_fo,[_fm]));});return [1,B(_d5(_fl,function(_fq){return E(_fp);}))];},_fr=new T(function(){return B(unCStr("SYN"));}),_fs=22,_ft=function(_fu){var _fv=new T(function(){return B(A(_fu,[_fs]));});return [1,B(_d5(_fr,function(_fw){return E(_fv);}))];},_fx=new T(function(){return B(unCStr("ETB"));}),_fy=23,_fz=function(_fA){var _fB=new T(function(){return B(A(_fA,[_fy]));});return [1,B(_d5(_fx,function(_fC){return E(_fB);}))];},_fD=new T(function(){return B(unCStr("CAN"));}),_fE=24,_fF=function(_fG){var _fH=new T(function(){return B(A(_fG,[_fE]));});return [1,B(_d5(_fD,function(_fI){return E(_fH);}))];},_fJ=new T(function(){return B(unCStr("EM"));}),_fK=25,_fL=function(_fM){var _fN=new T(function(){return B(A(_fM,[_fK]));});return [1,B(_d5(_fJ,function(_fO){return E(_fN);}))];},_fP=new T(function(){return B(unCStr("SUB"));}),_fQ=26,_fR=function(_fS){var _fT=new T(function(){return B(A(_fS,[_fQ]));});return [1,B(_d5(_fP,function(_fU){return E(_fT);}))];},_fV=new T(function(){return B(unCStr("ESC"));}),_fW=27,_fX=function(_fY){var _fZ=new T(function(){return B(A(_fY,[_fW]));});return [1,B(_d5(_fV,function(_g0){return E(_fZ);}))];},_g1=new T(function(){return B(unCStr("FS"));}),_g2=28,_g3=function(_g4){var _g5=new T(function(){return B(A(_g4,[_g2]));});return [1,B(_d5(_g1,function(_g6){return E(_g5);}))];},_g7=new T(function(){return B(unCStr("GS"));}),_g8=29,_g9=function(_ga){var _gb=new T(function(){return B(A(_ga,[_g8]));});return [1,B(_d5(_g7,function(_gc){return E(_gb);}))];},_gd=new T(function(){return B(unCStr("RS"));}),_ge=30,_gf=function(_gg){var _gh=new T(function(){return B(A(_gg,[_ge]));});return [1,B(_d5(_gd,function(_gi){return E(_gh);}))];},_gj=new T(function(){return B(unCStr("US"));}),_gk=31,_gl=function(_gm){var _gn=new T(function(){return B(A(_gm,[_gk]));});return [1,B(_d5(_gj,function(_go){return E(_gn);}))];},_gp=new T(function(){return B(unCStr("SP"));}),_gq=32,_gr=function(_gs){var _gt=new T(function(){return B(A(_gs,[_gq]));});return [1,B(_d5(_gp,function(_gu){return E(_gt);}))];},_gv=new T(function(){return B(unCStr("DEL"));}),_gw=127,_gx=function(_gy){var _gz=new T(function(){return B(A(_gy,[_gw]));});return [1,B(_d5(_gv,function(_gA){return E(_gz);}))];},_gB=[1,_gx,_1l],_gC=[1,_gr,_gB],_gD=[1,_gl,_gC],_gE=[1,_gf,_gD],_gF=[1,_g9,_gE],_gG=[1,_g3,_gF],_gH=[1,_fX,_gG],_gI=[1,_fR,_gH],_gJ=[1,_fL,_gI],_gK=[1,_fF,_gJ],_gL=[1,_fz,_gK],_gM=[1,_ft,_gL],_gN=[1,_fn,_gM],_gO=[1,_fh,_gN],_gP=[1,_fb,_gO],_gQ=[1,_f5,_gP],_gR=[1,_eZ,_gQ],_gS=[1,_eT,_gR],_gT=[1,_eN,_gS],_gU=[1,_eH,_gT],_gV=[1,_eB,_gU],_gW=[1,_ev,_gV],_gX=[1,_ep,_gW],_gY=[1,_ej,_gX],_gZ=[1,_ed,_gY],_h0=[1,_e7,_gZ],_h1=[1,_e1,_h0],_h2=[1,_dV,_h1],_h3=[1,_dP,_h2],_h4=[1,_dJ,_h3],_h5=[1,_dD,_h4],_h6=[1,_dx,_h5],_h7=[1,_dt,_h6],_h8=new T(function(){return B(_cX(_h7));}),_h9=34,_ha=[0,1114111],_hb=92,_hc=39,_hd=function(_he){var _hf=new T(function(){return B(A(_he,[_e6]));}),_hg=new T(function(){return B(A(_he,[_ec]));}),_hh=new T(function(){return B(A(_he,[_ei]));}),_hi=new T(function(){return B(A(_he,[_eo]));}),_hj=new T(function(){return B(A(_he,[_eu]));}),_hk=new T(function(){return B(A(_he,[_eA]));}),_hl=new T(function(){return B(A(_he,[_eG]));}),_hm=new T(function(){return B(A(_he,[_hb]));}),_hn=new T(function(){return B(A(_he,[_hc]));}),_ho=new T(function(){return B(A(_he,[_h9]));}),_hp=new T(function(){var _hq=function(_hr){var _hs=new T(function(){return B(_bg(E(_hr)));}),_ht=function(_hu){var _hv=B(_bQ(_hs,_hu));if(!B(_cN(_hv,_ha))){return [2];}else{return new F(function(){return A(_he,[new T(function(){var _hw=B(_cK(_hv));if(_hw>>>0>1114111){return B(_cI(_hw));}else{return _hw;}})]);});}};return [1,B(_9O(_hr,_ht))];},_hx=new T(function(){var _hy=new T(function(){return B(A(_he,[_gk]));}),_hz=new T(function(){return B(A(_he,[_ge]));}),_hA=new T(function(){return B(A(_he,[_g8]));}),_hB=new T(function(){return B(A(_he,[_g2]));}),_hC=new T(function(){return B(A(_he,[_fW]));}),_hD=new T(function(){return B(A(_he,[_fQ]));}),_hE=new T(function(){return B(A(_he,[_fK]));}),_hF=new T(function(){return B(A(_he,[_fE]));}),_hG=new T(function(){return B(A(_he,[_fy]));}),_hH=new T(function(){return B(A(_he,[_fs]));}),_hI=new T(function(){return B(A(_he,[_fm]));}),_hJ=new T(function(){return B(A(_he,[_fg]));}),_hK=new T(function(){return B(A(_he,[_fa]));}),_hL=new T(function(){return B(A(_he,[_f4]));}),_hM=new T(function(){return B(A(_he,[_eY]));}),_hN=new T(function(){return B(A(_he,[_eS]));}),_hO=new T(function(){return B(A(_he,[_eM]));}),_hP=new T(function(){return B(A(_he,[_di]));}),_hQ=new T(function(){return B(A(_he,[_e0]));}),_hR=new T(function(){return B(A(_he,[_dU]));}),_hS=new T(function(){return B(A(_he,[_dO]));}),_hT=new T(function(){return B(A(_he,[_dI]));}),_hU=new T(function(){return B(A(_he,[_dC]));}),_hV=new T(function(){return B(A(_he,[_do]));}),_hW=new T(function(){return B(A(_he,[_dw]));}),_hX=function(_hY){switch(E(_hY)){case 64:return E(_hW);case 65:return E(_hV);case 66:return E(_hU);case 67:return E(_hT);case 68:return E(_hS);case 69:return E(_hR);case 70:return E(_hQ);case 71:return E(_hf);case 72:return E(_hg);case 73:return E(_hh);case 74:return E(_hi);case 75:return E(_hj);case 76:return E(_hk);case 77:return E(_hl);case 78:return E(_hP);case 79:return E(_hO);case 80:return E(_hN);case 81:return E(_hM);case 82:return E(_hL);case 83:return E(_hK);case 84:return E(_hJ);case 85:return E(_hI);case 86:return E(_hH);case 87:return E(_hG);case 88:return E(_hF);case 89:return E(_hE);case 90:return E(_hD);case 91:return E(_hC);case 92:return E(_hB);case 93:return E(_hA);case 94:return E(_hz);case 95:return E(_hy);default:return [2];}};return B(_82([0,function(_hZ){return (E(_hZ)==94)?[0,_hX]:[2];}],new T(function(){return B(A(_h8,[_he]));})));});return B(_82([1,B(_97(_cE,_cG,_hq))],_hx));});return new F(function(){return _82([0,function(_i0){switch(E(_i0)){case 34:return E(_ho);case 39:return E(_hn);case 92:return E(_hm);case 97:return E(_hf);case 98:return E(_hg);case 102:return E(_hk);case 110:return E(_hi);case 114:return E(_hl);case 116:return E(_hh);case 118:return E(_hj);default:return [2];}}],_hp);});},_i1=function(_i2){return new F(function(){return A(_i2,[_a]);});},_i3=function(_i4){var _i5=E(_i4);if(!_i5[0]){return E(_i1);}else{var _i6=E(_i5[1]),_i7=_i6>>>0,_i8=new T(function(){return B(_i3(_i5[2]));});if(_i7>887){var _i9=u_iswspace(_i6);if(!E(_i9)){return E(_i1);}else{var _ia=function(_ib){var _ic=new T(function(){return B(A(_i8,[_ib]));});return [0,function(_id){return E(_ic);}];};return E(_ia);}}else{var _ie=E(_i7);if(_ie==32){var _if=function(_ig){var _ih=new T(function(){return B(A(_i8,[_ig]));});return [0,function(_ii){return E(_ih);}];};return E(_if);}else{if(_ie-9>>>0>4){if(E(_ie)==160){var _ij=function(_ik){var _il=new T(function(){return B(A(_i8,[_ik]));});return [0,function(_im){return E(_il);}];};return E(_ij);}else{return E(_i1);}}else{var _in=function(_io){var _ip=new T(function(){return B(A(_i8,[_io]));});return [0,function(_iq){return E(_ip);}];};return E(_in);}}}}},_ir=function(_is){var _it=new T(function(){return B(_ir(_is));}),_iu=function(_iv){return (E(_iv)==92)?E(_it):[2];},_iw=function(_ix){return [0,_iu];},_iy=[1,function(_iz){return new F(function(){return A(_i3,[_iz,_iw]);});}],_iA=new T(function(){return B(_hd(function(_iB){return new F(function(){return A(_is,[[0,_iB,_cy]]);});}));}),_iC=function(_iD){var _iE=E(_iD);if(_iE==38){return E(_it);}else{var _iF=_iE>>>0;if(_iF>887){var _iG=u_iswspace(_iE);return (E(_iG)==0)?[2]:E(_iy);}else{var _iH=E(_iF);return (_iH==32)?E(_iy):(_iH-9>>>0>4)?(E(_iH)==160)?E(_iy):[2]:E(_iy);}}};return new F(function(){return _82([0,function(_iI){return (E(_iI)==92)?[0,_iC]:[2];}],[0,function(_iJ){var _iK=E(_iJ);if(E(_iK)==92){return E(_iA);}else{return new F(function(){return A(_is,[[0,_iK,_cx]]);});}}]);});},_iL=function(_iM,_iN){var _iO=new T(function(){return B(A(_iN,[[1,new T(function(){return B(A(_iM,[_1l]));})]]));}),_iP=function(_iQ){var _iR=E(_iQ),_iS=E(_iR[1]);if(E(_iS)==34){if(!E(_iR[2])){return E(_iO);}else{return new F(function(){return _iL(function(_iT){return new F(function(){return A(_iM,[[1,_iS,_iT]]);});},_iN);});}}else{return new F(function(){return _iL(function(_iU){return new F(function(){return A(_iM,[[1,_iS,_iU]]);});},_iN);});}};return new F(function(){return _ir(_iP);});},_iV=new T(function(){return B(unCStr("_\'"));}),_iW=function(_iX){var _iY=u_iswalnum(_iX);if(!E(_iY)){return new F(function(){return _cp(_8D,_iX,_iV);});}else{return true;}},_iZ=function(_j0){return new F(function(){return _iW(E(_j0));});},_j1=new T(function(){return B(unCStr(",;()[]{}`"));}),_j2=new T(function(){return B(unCStr("=>"));}),_j3=[1,_j2,_1l],_j4=new T(function(){return B(unCStr("~"));}),_j5=[1,_j4,_j3],_j6=new T(function(){return B(unCStr("@"));}),_j7=[1,_j6,_j5],_j8=new T(function(){return B(unCStr("->"));}),_j9=[1,_j8,_j7],_ja=new T(function(){return B(unCStr("<-"));}),_jb=[1,_ja,_j9],_jc=new T(function(){return B(unCStr("|"));}),_jd=[1,_jc,_jb],_je=new T(function(){return B(unCStr("\\"));}),_jf=[1,_je,_jd],_jg=new T(function(){return B(unCStr("="));}),_jh=[1,_jg,_jf],_ji=new T(function(){return B(unCStr("::"));}),_jj=[1,_ji,_jh],_jk=new T(function(){return B(unCStr(".."));}),_jl=[1,_jk,_jj],_jm=function(_jn){var _jo=new T(function(){return B(A(_jn,[_9L]));}),_jp=new T(function(){var _jq=new T(function(){var _jr=function(_js){var _jt=new T(function(){return B(A(_jn,[[0,_js]]));});return [0,function(_ju){return (E(_ju)==39)?E(_jt):[2];}];};return B(_hd(_jr));}),_jv=function(_jw){var _jx=E(_jw);switch(E(_jx)){case 39:return [2];case 92:return E(_jq);default:var _jy=new T(function(){return B(A(_jn,[[0,_jx]]));});return [0,function(_jz){return (E(_jz)==39)?E(_jy):[2];}];}},_jA=new T(function(){var _jB=new T(function(){return B(_iL(_Q,_jn));}),_jC=new T(function(){var _jD=new T(function(){var _jE=new T(function(){var _jF=function(_jG){var _jH=E(_jG),_jI=u_iswalpha(_jH);return (E(_jI)==0)?(E(_jH)==95)?[1,B(_9x(_iZ,function(_jJ){return new F(function(){return A(_jn,[[3,[1,_jH,_jJ]]]);});}))]:[2]:[1,B(_9x(_iZ,function(_jK){return new F(function(){return A(_jn,[[3,[1,_jH,_jK]]]);});}))];};return B(_82([0,_jF],new T(function(){return [1,B(_97(_aJ,_cn,_jn))];})));}),_jL=function(_jM){return (!B(_cp(_8D,_jM,_cu)))?[2]:[1,B(_9x(_cv,function(_jN){var _jO=[1,_jM,_jN];if(!B(_cp(_8M,_jO,_jl))){return new F(function(){return A(_jn,[[4,_jO]]);});}else{return new F(function(){return A(_jn,[[2,_jO]]);});}}))];};return B(_82([0,_jL],_jE));});return B(_82([0,function(_jP){if(!B(_cp(_8D,_jP,_j1))){return [2];}else{return new F(function(){return A(_jn,[[2,[1,_jP,_1l]]]);});}}],_jD));});return B(_82([0,function(_jQ){return (E(_jQ)==34)?E(_jB):[2];}],_jC));});return B(_82([0,function(_jR){return (E(_jR)==39)?[0,_jv]:[2];}],_jA));});return new F(function(){return _82([1,function(_jS){return (E(_jS)[0]==0)?E(_jo):[2];}],_jp);});},_jT=0,_jU=function(_jV,_jW){var _jX=new T(function(){var _jY=new T(function(){var _jZ=function(_k0){var _k1=new T(function(){var _k2=new T(function(){return B(A(_jW,[_k0]));});return B(_jm(function(_k3){var _k4=E(_k3);return (_k4[0]==2)?(!B(_2b(_k4[1],_8w)))?[2]:E(_k2):[2];}));}),_k5=function(_k6){return E(_k1);};return [1,function(_k7){return new F(function(){return A(_i3,[_k7,_k5]);});}];};return B(A(_jV,[_jT,_jZ]));});return B(_jm(function(_k8){var _k9=E(_k8);return (_k9[0]==2)?(!B(_2b(_k9[1],_8v)))?[2]:E(_jY):[2];}));}),_ka=function(_kb){return E(_jX);};return function(_kc){return new F(function(){return A(_i3,[_kc,_ka]);});};},_kd=function(_ke,_kf){var _kg=function(_kh){var _ki=new T(function(){return B(A(_ke,[_kh]));}),_kj=function(_kk){return new F(function(){return _82(B(A(_ki,[_kk])),new T(function(){return [1,B(_jU(_kg,_kk))];}));});};return E(_kj);},_kl=new T(function(){return B(A(_ke,[_kf]));}),_km=function(_kn){return new F(function(){return _82(B(A(_kl,[_kn])),new T(function(){return [1,B(_jU(_kg,_kn))];}));});};return E(_km);},_ko=function(_kp,_kq){return new F(function(){return A(_kq,[_2P]);});},_kr=[0,_2U,_ko],_ks=[1,_kr,_1l],_kt=function(_ku,_kv){return new F(function(){return A(_kv,[_2R]);});},_kw=[0,_2T,_kt],_kx=[1,_kw,_ks],_ky=function(_kz,_kA,_kB){var _kC=E(_kz);if(!_kC[0]){return [2];}else{var _kD=E(_kC[1]),_kE=_kD[1],_kF=new T(function(){return B(A(_kD[2],[_kA,_kB]));}),_kG=new T(function(){return B(_jm(function(_kH){var _kI=E(_kH);switch(_kI[0]){case 3:return (!B(_2b(_kE,_kI[1])))?[2]:E(_kF);case 4:return (!B(_2b(_kE,_kI[1])))?[2]:E(_kF);default:return [2];}}));}),_kJ=function(_kK){return E(_kG);};return new F(function(){return _82([1,function(_kL){return new F(function(){return A(_i3,[_kL,_kJ]);});}],new T(function(){return B(_ky(_kC[2],_kA,_kB));}));});}},_kM=function(_kN,_kO){return new F(function(){return _ky(_kx,_kN,_kO);});},_kP=function(_kQ){return new F(function(){return _kd(_kM,_kQ);});},_kR=new T(function(){return B(unCStr("["));}),_kS=function(_kT,_kU){var _kV=function(_kW,_kX){var _kY=new T(function(){return B(A(_kX,[_1l]));}),_kZ=new T(function(){var _l0=function(_l1){return new F(function(){return _kV(_cy,function(_l2){return new F(function(){return A(_kX,[[1,_l1,_l2]]);});});});};return B(A(_kT,[_jT,_l0]));}),_l3=new T(function(){return B(_jm(function(_l4){var _l5=E(_l4);if(_l5[0]==2){var _l6=E(_l5[1]);if(!_l6[0]){return [2];}else{var _l7=_l6[2];switch(E(_l6[1])){case 44:return (E(_l7)[0]==0)?(!E(_kW))?[2]:E(_kZ):[2];case 93:return (E(_l7)[0]==0)?E(_kY):[2];default:return [2];}}}else{return [2];}}));}),_l8=function(_l9){return E(_l3);};return [1,function(_la){return new F(function(){return A(_i3,[_la,_l8]);});}];},_lb=function(_lc,_ld){return new F(function(){return _le(_ld);});},_lf=_kU,_lg=new T(function(){var _lh=new T(function(){var _li=new T(function(){var _lj=function(_lk){return new F(function(){return _kV(_cy,function(_ll){return new F(function(){return A(_lf,[[1,_lk,_ll]]);});});});};return B(A(_kT,[_jT,_lj]));});return B(_82(B(_kV(_cx,_lf)),_li));});return B(_jm(function(_lm){var _ln=E(_lm);return (_ln[0]==2)?(!B(_2b(_ln[1],_kR)))?[2]:E(_lh):[2];}));}),_lo=function(_lp){return E(_lg);};return new F(function(){return _82([1,function(_lq){return new F(function(){return A(_i3,[_lq,_lo]);});}],new T(function(){return [1,B(_jU(_lb,_lf))];}));});},_lr=function(_ls,_lt){return new F(function(){return _kS(_kP,_lt);});},_lu=new T(function(){return B(_kS(_kP,_8Z));}),_lv=function(_kQ){return new F(function(){return _7S(_lu,_kQ);});},_lw=function(_lx){var _ly=new T(function(){return B(A(_kd,[_kM,_lx,_8Z]));});return function(_lz){return new F(function(){return _7S(_ly,_lz);});};},_lA=[0,_lw,_lv,_kP,_lr],_lB=function(_lC,_lD){return new F(function(){return _lE(_lD);});},_lE=function(_lF){var _lG=new T(function(){return B(_jm(function(_lH){var _lI=E(_lH);if(!_lI[0]){return new F(function(){return A(_lF,[_lI[1]]);});}else{return [2];}}));}),_lJ=function(_lK){return E(_lG);};return new F(function(){return _82([1,function(_lL){return new F(function(){return A(_i3,[_lL,_lJ]);});}],new T(function(){return [1,B(_jU(_lB,_lF))];}));});},_lM=function(_lN,_lO){return new F(function(){return _lE(_lO);});},_lP=function(_lQ,_lR){return new F(function(){return _lS(_lR);});},_lS=function(_lT){var _lU=new T(function(){return B(_jm(function(_lV){var _lW=E(_lV);if(_lW[0]==1){return new F(function(){return A(_lT,[_lW[1]]);});}else{return [2];}}));}),_lX=function(_lY){return E(_lU);};return new F(function(){return _82(B(_82([1,function(_lZ){return new F(function(){return A(_i3,[_lZ,_lX]);});}],new T(function(){return B(_kS(_lM,_lT));}))),new T(function(){return [1,B(_jU(_lP,_lT))];}));});},_m0=function(_m1,_m2){return new F(function(){return _lS(_m2);});},_m3=function(_m4,_m5){return new F(function(){return _kS(_m0,_m5);});},_m6=new T(function(){return B(_kS(_m0,_8Z));}),_m7=function(_m8){return new F(function(){return _7S(_m6,_m8);});},_m9=new T(function(){return B(_lS(_8Z));}),_ma=function(_m8){return new F(function(){return _7S(_m9,_m8);});},_mb=function(_mc,_m8){return new F(function(){return _ma(_m8);});},_md=[0,_mb,_m7,_m0,_m3],_me=function(_mf,_mg){var _mh=E(_mg);return (_mh[0]==0)?[0]:[1,new T(function(){return B(A(_mf,[_mh[1]]));})];},_mi=function(_mj,_mk,_){var _ml=B(A(_mk,[_]));return new T(function(){return B(_me(_mj,_ml));});},_mm=function(_mn,_mo,_){var _mp=B(A(_mo,[_]));return new T(function(){if(!E(_mp)[0]){return [0];}else{return [1,_mn];}});},_mq=[0,_mi,_mm],_mr=function(_ms,_mt,_){var _mu=B(A(_ms,[_]));if(!E(_mu)[0]){return _6J;}else{var _mv=B(A(_mt,[_]));return (E(_mv)[0]==0)?_6J:_mv;}},_mw=function(_mx,_my,_){var _mz=B(A(_mx,[_])),_mA=E(_mz);if(!_mA[0]){return _6J;}else{var _mB=B(A(_my,[_]));return (E(_mB)[0]==0)?_6J:_mA;}},_mC=function(_mD,_){return [1,_mD];},_mE=function(_mF){return E(E(_mF)[2]);},_mG=function(_mH){return E(E(_mH)[4]);},_mI=function(_mJ,_mK){return new F(function(){return A(_mE,[_mJ,new T(function(){return B(A(_mG,[_mJ,_mK]));}),function(_mL){return new F(function(){return A(_mG,[_mJ,[1,_mL]]);});}]);});},_mM=function(_mN,_mO,_mP,_mQ){var _mR=new T(function(){return B(A(_mG,[_mO,_6J]));}),_mS=function(_mT){var _mU=E(_mT);if(!_mU[0]){return E(_mR);}else{var _mV=function(_mW){var _mX=E(_mW);if(!_mX[0]){return E(_mR);}else{return new F(function(){return _mI(_mO,new T(function(){return B(A(_mU[1],[_mX[1]]));}));});}};return new F(function(){return A(_mE,[_mO,_mQ,_mV]);});}};return new F(function(){return A(_mE,[_mO,_mP,_mS]);});},_mY=function(_mZ,_n0){return new F(function(){return _mM(_mq,_6Q,_mZ,_n0);});},_n1=[0,_mq,_mC,_mY,_mr,_mw],_n2=function(_n3,_n4,_){var _n5=B(A(_n3,[_]));if(!E(_n5)[0]){return _6J;}else{return new F(function(){return A(_n4,[_]);});}},_n6=function(_n7,_mZ,_){return new F(function(){return _n2(_n7,_mZ,_);});},_n8=function(_n9,_na,_){var _nb=B(A(_n9,[_])),_nc=E(_nb);if(!_nc[0]){return _6J;}else{return new F(function(){return A(_na,[_nc[1],_]);});}},_nd=function(_ne,_){return _6J;},_nf=[0,_n1,_n8,_n6,_mC,_nd],_ng=function(_nh,_){return [1,B(A(_nh,[_]))];},_ni=[0,_nf,_ng],_nj=function(_nk,_nl,_nm,_nn,_no,_np,_nq,_nr){if(_nk!=_no){return false;}else{if(E(_nl)!=E(_np)){return false;}else{var _ns=E(_nm),_nt=E(_nq);if(E(_ns[1])!=E(_nt[1])){return false;}else{if(E(_ns[2])!=E(_nt[2])){return false;}else{return new F(function(){return _2b(_nn,_nr);});}}}}},_nu=function(_nv,_nw){var _nx=E(_nv),_ny=E(_nx[1]),_nz=E(_nw),_nA=E(_nz[1]);return new F(function(){return _nj(E(_ny[1]),_ny[2],_nx[2],_nx[3],E(_nA[1]),_nA[2],_nz[2],_nz[3]);});},_nB="scans",_nC=[1,_nB,_1l],_nD="calib",_nE=[1,_nD,_nC],_nF=function(_nG){var _nH=E(_nG);return [3,[1,new T(function(){return B(_2J(_nH[1]));}),[1,new T(function(){return B(_2J(_nH[2]));}),_1l]]];},_nI=new T(function(){return [1,"Dragging"];}),_nJ=[0,_1Y,_nI],_nK=new T(function(){return [1,"Free"];}),_nL="state",_nM=[0,_nL,_nK],_nN=[1,_nM,_1l],_nO=[4,E(_nN)],_nP=function(_nQ,_nR){switch(E(_nQ)){case 0:return new F(function(){return _16(_29,_nR);});break;case 1:return new F(function(){return _16(_2a,_nR);});break;case 2:return new F(function(){return _16(_27,_nR);});break;default:return new F(function(){return _16(_28,_nR);});}},_nS=function(_nT){return E(toJSStr(B(_nP(_nT,_1l))));},_nU=function(_nV){return [1,B(_nS(_nV))];},_nW=function(_nX){var _nY=new T(function(){var _nZ=E(E(_nX)[2]);return [3,[1,new T(function(){return B(_nF(_nZ[1]));}),[1,new T(function(){return B(_nF(_nZ[2]));}),[1,new T(function(){return B(_nF(_nZ[3]));}),[1,new T(function(){return B(_nF(_nZ[4]));}),_1l]]]]];}),_o0=new T(function(){var _o1=E(E(_nX)[1]);if(!_o1[0]){return E(_nO);}else{return [4,[1,_nJ,[1,[0,_1T,new T(function(){return B(_nU(_o1[1]));})],_1l]]];}});return [1,[0,_1S,_o0],[1,[0,_1R,_nY],_1l]];},_o2="mouse",_o3="scans",_o4="top",_o5="bottom",_o6="offset",_o7="choice",_o8="step",_o9="rotations",_oa=[1,_o9,_1l],_ob=[1,_o8,_oa],_oc=[1,_o7,_ob],_od=[1,_o6,_oc],_oe=[1,_o5,_od],_of=[1,_o4,_oe],_og=[1,_o3,_of],_oh=[1,_o2,_og],_oi=function(_oj,_ok){var _ol=E(_oj);if(!_ol[0]){return [0];}else{var _om=E(_ok);return (_om[0]==0)?[0]:[1,[0,_ol[1],_om[1]],new T(function(){return B(_oi(_ol[2],_om[2]));})];}},_on=function(_oo){return new F(function(){return _oi(_oh,[1,new T(function(){if(!E(E(_oo)[1])){return [1,toJSStr(E(_33))];}else{return [1,toJSStr(E(_34))];}}),[1,new T(function(){return [3,E(B(_bc(_3B,E(_oo)[2])))];}),[1,new T(function(){return [0,E(E(_oo)[3])];}),[1,new T(function(){return [0,E(E(_oo)[4])];}),[1,new T(function(){return [0,E(E(_oo)[5])];}),[1,new T(function(){if(!E(E(_oo)[6])){return [1,toJSStr(E(_2T))];}else{return [1,toJSStr(E(_2U))];}}),[1,new T(function(){return [0,E(E(_oo)[7])];}),[1,new T(function(){return [3,E(B(_bc(_2J,E(_oo)[8])))];}),_1l]]]]]]]]);});},_op=function(_oq){return [1,E(_oq)];},_or="deltaZ",_os="deltaY",_ot="deltaX",_ou=new T(function(){return B(unCStr(")"));}),_ov=new T(function(){return B(_1g(0,2,_ou));}),_ow=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_ov));}),_ox=function(_oy){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_1g(0,_oy,_ow));}))));});},_oz=function(_oA,_){return new T(function(){var _oB=Number(E(_oA)),_oC=jsTrunc(_oB);if(_oC<0){return B(_ox(_oC));}else{if(_oC>2){return B(_ox(_oC));}else{return _oC;}}});},_oD=0,_oE=[0,_oD,_oD,_oD],_oF="button",_oG=new T(function(){return jsGetMouseCoords;}),_oH=function(_oI,_){var _oJ=E(_oI);if(!_oJ[0]){return _1l;}else{var _oK=B(_oH(_oJ[2],_));return [1,new T(function(){var _oL=Number(E(_oJ[1]));return jsTrunc(_oL);}),_oK];}},_oM=function(_oN,_){var _oO=__arr2lst(0,_oN);return new F(function(){return _oH(_oO,_);});},_oP=function(_oQ,_){return new F(function(){return _oM(E(_oQ),_);});},_oR=function(_oS,_){return new T(function(){var _oT=Number(E(_oS));return jsTrunc(_oT);});},_oU=[0,_oR,_oP],_oV=function(_oW,_){var _oX=E(_oW);if(!_oX[0]){return _1l;}else{var _oY=B(_oV(_oX[2],_));return [1,_oX[1],_oY];}},_oZ=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_p0=[0,_6J,_6K,_1l,_oZ,_6J,_6J],_p1=new T(function(){return B(_6H(_p0));}),_p2=function(_){return new F(function(){return die(_p1);});},_p3=function(_p4){return E(E(_p4)[1]);},_p5=function(_p6,_p7,_p8,_){var _p9=__arr2lst(0,_p8),_pa=B(_oV(_p9,_)),_pb=E(_pa);if(!_pb[0]){return new F(function(){return _p2(_);});}else{var _pc=E(_pb[2]);if(!_pc[0]){return new F(function(){return _p2(_);});}else{if(!E(_pc[2])[0]){var _pd=B(A(_p3,[_p6,_pb[1],_])),_pe=B(A(_p3,[_p7,_pc[1],_]));return [0,_pd,_pe];}else{return new F(function(){return _p2(_);});}}}},_pf=function(_){return new F(function(){return __jsNull();});},_pg=function(_ph){var _pi=B(A(_ph,[_]));return E(_pi);},_pj=new T(function(){return B(_pg(_pf));}),_pk=new T(function(){return E(_pj);}),_pl=function(_pm,_pn,_){if(E(_pm)==7){var _po=E(_oG)(_pn),_pp=B(_p5(_oU,_oU,_po,_)),_pq=_pn[E(_ot)],_pr=_pn[E(_os)],_ps=_pn[E(_or)];return new T(function(){return [0,E(_pp),E(_6J),[0,_pq,_pr,_ps]];});}else{var _pt=E(_oG)(_pn),_pu=B(_p5(_oU,_oU,_pt,_)),_pv=_pn[E(_oF)],_pw=__eq(_pv,E(_pk));if(!E(_pw)){var _px=B(_oz(_pv,_));return new T(function(){return [0,E(_pu),[1,_px],E(_oE)];});}else{return new T(function(){return [0,E(_pu),E(_6J),E(_oE)];});}}},_py=function(_pz,_pA,_){return new F(function(){return _pl(_pz,E(_pA),_);});},_pB="mouseout",_pC="mouseover",_pD="mousemove",_pE="mouseup",_pF="mousedown",_pG="dblclick",_pH="click",_pI="wheel",_pJ=function(_pK){switch(E(_pK)){case 0:return E(_pH);case 1:return E(_pG);case 2:return E(_pF);case 3:return E(_pE);case 4:return E(_pD);case 5:return E(_pC);case 6:return E(_pB);default:return E(_pI);}},_pL=[0,_pJ,_py],_pM=function(_){return new F(function(){return E(_4)("td");});},_pN=function(_pO){return E(E(_pO)[1]);},_pP=function(_pQ){return E(E(_pQ)[3]);},_pR=(function(c,p){p.appendChild(c);}),_pS=function(_pT){return E(E(_pT)[1]);},_pU=(function(e,p,v){e.setAttribute(p, v);}),_pV=(function(e,p,v){e.style[p] = v;}),_pW=function(_pX,_pY,_pZ,_q0){var _q1=new T(function(){return B(A(_pS,[_pX,_pZ]));}),_q2=function(_q3,_){var _q4=E(_q3);if(!_q4[0]){return _a;}else{var _q5=E(_q1),_q6=E(_pR),_q7=_q6(E(_q4[1]),_q5),_q8=_q4[2];while(1){var _q9=E(_q8);if(!_q9[0]){return _a;}else{var _qa=_q6(E(_q9[1]),_q5);_q8=_q9[2];continue;}}}},_qb=function(_qc,_){while(1){var _qd=B((function(_qe,_){var _qf=E(_qe);if(!_qf[0]){return _a;}else{var _qg=_qf[2],_qh=E(_qf[1]);if(!_qh[0]){var _qi=_qh[2],_qj=E(_qh[1]);switch(_qj[0]){case 0:var _qk=E(_q1),_ql=E(_1),_qm=_ql(_qk,_qj[1],_qi),_qn=_qg;while(1){var _qo=E(_qn);if(!_qo[0]){return _a;}else{var _qp=_qo[2],_qq=E(_qo[1]);if(!_qq[0]){var _qr=_qq[2],_qs=E(_qq[1]);switch(_qs[0]){case 0:var _qt=_ql(_qk,_qs[1],_qr);_qn=_qp;continue;case 1:var _qu=E(_pV)(_qk,_qs[1],_qr);_qn=_qp;continue;default:var _qv=E(_pU)(_qk,_qs[1],_qr);_qn=_qp;continue;}}else{var _qw=B(_q2(_qq[1],_));_qn=_qp;continue;}}}break;case 1:var _qx=E(_q1),_qy=E(_pV),_qz=_qy(_qx,_qj[1],_qi),_qA=_qg;while(1){var _qB=E(_qA);if(!_qB[0]){return _a;}else{var _qC=_qB[2],_qD=E(_qB[1]);if(!_qD[0]){var _qE=_qD[2],_qF=E(_qD[1]);switch(_qF[0]){case 0:var _qG=E(_1)(_qx,_qF[1],_qE);_qA=_qC;continue;case 1:var _qH=_qy(_qx,_qF[1],_qE);_qA=_qC;continue;default:var _qI=E(_pU)(_qx,_qF[1],_qE);_qA=_qC;continue;}}else{var _qJ=B(_q2(_qD[1],_));_qA=_qC;continue;}}}break;default:var _qK=E(_q1),_qL=E(_pU),_qM=_qL(_qK,_qj[1],_qi),_qN=_qg;while(1){var _qO=E(_qN);if(!_qO[0]){return _a;}else{var _qP=_qO[2],_qQ=E(_qO[1]);if(!_qQ[0]){var _qR=_qQ[2],_qS=E(_qQ[1]);switch(_qS[0]){case 0:var _qT=E(_1)(_qK,_qS[1],_qR);_qN=_qP;continue;case 1:var _qU=E(_pV)(_qK,_qS[1],_qR);_qN=_qP;continue;default:var _qV=_qL(_qK,_qS[1],_qR);_qN=_qP;continue;}}else{var _qW=B(_q2(_qQ[1],_));_qN=_qP;continue;}}}}}else{var _qX=B(_q2(_qh[1],_));_qc=_qg;return null;}}})(_qc,_));if(_qd!=null){return _qd;}}};return new F(function(){return A(_2,[_pY,function(_){return new F(function(){return _qb(_q0,_);});}]);});},_qY=function(_qZ,_r0,_r1,_r2){var _r3=B(_pN(_r0)),_r4=function(_r5){return new F(function(){return A(_pP,[_r3,new T(function(){return B(_pW(_qZ,_r0,_r5,_r2));}),new T(function(){return B(A(_mG,[_r3,_r5]));})]);});};return new F(function(){return A(_mE,[_r3,_r1,_r4]);});},_r6=function(_r7,_){var _r8=E(_r7);if(!_r8[0]){return _1l;}else{var _r9=B(A(_qY,[_S,_6R,_pM,[1,[1,[1,_r8[1],_1l]],_1l],_])),_ra=B(_r6(_r8[2],_));return [1,_r9,_ra];}},_rb=function(_rc,_rd,_){var _re=B(A(_qY,[_S,_6R,_pM,[1,[1,[1,_rc,_1l]],_1l],_])),_rf=B(_r6(_rd,_));return [1,_re,_rf];},_rg=(function(s){return document.createTextNode(s);}),_rh=function(_ri,_){var _rj=jsShow(_ri),_rk=E(_rg)(toJSStr(fromJSStr(_rj)));return new F(function(){return A(_qY,[_S,_6R,_pM,[1,[1,[1,_rk,_1l]],_1l],_]);});},_rl=function(_rm,_rn,_ro){var _rp=(_ro-_rn)*25/900;if(!_rp){var _rq=rintDouble(0/_rm);return _rq&4294967295;}else{if(_rp<=0){var _rr=rintDouble( -_rp/_rm);return _rr&4294967295;}else{var _rs=rintDouble(_rp/_rm);return _rs&4294967295;}}},_rt=function(_ru,_rv){return [0,E(_ru),toJSStr(E(_rv))];},_rw=2,_rx=0,_ry=new T(function(){return B(unCStr("x1"));}),_rz=new T(function(){return B(unCStr("y1"));}),_rA=new T(function(){return B(unCStr("x2"));}),_rB=new T(function(){return B(unCStr("y2"));}),_rC=new T(function(){return B(unCStr("frames"));}),_rD=new T(function(){return B(unCStr("time (minutes)"));}),_rE=new T(function(){return B(unCStr("title"));}),_rF=new T(function(){return B(unCStr("Delete"));}),_rG=[1,_rF,_1l],_rH=[1,_rE,_rG],_rI=[1,_rD,_rH],_rJ=[1,_rC,_rI],_rK=[1,_rB,_rJ],_rL=[1,_rA,_rK],_rM=function(_){return new F(function(){return E(_4)("span");});},_rN=new T(function(){return [0,[2,"class"],"glyphicon glyphicon-remove"];}),_rO=[1,_rN,_1l],_rP=new T(function(){return B(_qY(_S,_6R,_rM,_rO));}),_rQ=function(_){return new F(function(){return E(_4)("input");});},_rR=function(_){return new F(function(){return E(_4)("tr");});},_rS=function(_){return new F(function(){return E(_4)("th");});},_rT=function(_){return new F(function(){return E(_4)("button");});},_rU=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_rV=function(_rW){var _rX=I_decodeDouble(_rW);return [0,[1,_rX[2]],_rX[1]];},_rY=function(_rZ){var _s0=E(_rZ);if(!_s0[0]){return _s0[1];}else{return new F(function(){return I_toNumber(_s0[1]);});}},_s1=function(_s2){var _s3=hs_intToInt64(2147483647),_s4=hs_leInt64(_s2,_s3);if(!_s4){return [1,I_fromInt64(_s2)];}else{var _s5=hs_intToInt64(-2147483648),_s6=hs_geInt64(_s2,_s5);if(!_s6){return [1,I_fromInt64(_s2)];}else{var _s7=hs_int64ToInt(_s2);return new F(function(){return _bg(_s7);});}}},_s8=function(_s9){var _sa=hs_intToInt64(_s9);return E(_sa);},_sb=function(_sc){var _sd=E(_sc);if(!_sd[0]){return new F(function(){return _s8(_sd[1]);});}else{return new F(function(){return I_toInt64(_sd[1]);});}},_se=new T(function(){return [2,"value"];}),_sf=new T(function(){return [0,[2,"class"],"btn btn-danger"];}),_sg=new T(function(){return [0,[2,"type"],"text"];}),_sh=function(_si){return E(E(_si)[1]);},_sj=function(_sk){return E(E(_sk)[2]);},_sl=function(_sm){return E(E(_sm)[1]);},_sn=function(_){return new F(function(){return nMV(_6J);});},_so=new T(function(){return B(_pg(_sn));}),_sp=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_sq=function(_sr){return E(E(_sr)[2]);},_ss=function(_st,_su,_sv,_sw,_sx,_sy){var _sz=B(_sh(_st)),_sA=B(_pN(_sz)),_sB=new T(function(){return B(_2(_sz));}),_sC=new T(function(){return B(_mG(_sA));}),_sD=new T(function(){return B(A(_pS,[_su,_sw]));}),_sE=new T(function(){return B(A(_sl,[_sv,_sx]));}),_sF=function(_sG){return new F(function(){return A(_sC,[[0,_sE,_sD,_sG]]);});},_sH=function(_sI){var _sJ=new T(function(){var _sK=new T(function(){var _sL=__createJSFunc(2,function(_sM,_){var _sN=B(A(E(_sI),[_sM,_]));return _pk;}),_sO=_sL;return function(_){return new F(function(){return E(_sp)(E(_sD),E(_sE),_sO);});};});return B(A(_sB,[_sK]));});return new F(function(){return A(_mE,[_sA,_sJ,_sF]);});},_sP=new T(function(){var _sQ=new T(function(){return B(_2(_sz));}),_sR=function(_sS){var _sT=new T(function(){return B(A(_sQ,[function(_){var _=wMV(E(_so),[1,_sS]);return new F(function(){return A(_sj,[_sv,_sx,_sS,_]);});}]));});return new F(function(){return A(_mE,[_sA,_sT,_sy]);});};return B(A(_sq,[_st,_sR]));});return new F(function(){return A(_mE,[_sA,_sP,_sH]);});},_sU=function(_sV,_sW){while(1){var _sX=E(_sV);if(!_sX[0]){return E(_sW);}else{var _sY=[1,_sX[1],_sW];_sV=_sX[2];_sW=_sY;continue;}}},_sZ=function(_t0,_t1){while(1){var _t2=E(_t0);if(!_t2[0]){_t0=[1,I_fromInt(_t2[1])];continue;}else{return [1,I_shiftLeft(_t2[1],_t1)];}}},_t3=function(_t4,_t5,_t6,_t7,_){var _t8=E(_rU)(_t7),_t9=E(_rg),_ta=_t9(toJSStr(E(_ry))),_tb=B(A(_qY,[_S,_6R,_rS,[1,[1,[1,_ta,_1l]],_1l],_])),_tc=function(_td,_){var _te=E(_td);if(!_te[0]){return _1l;}else{var _tf=_t9(toJSStr(E(_te[1]))),_tg=B(A(_qY,[_S,_6R,_rS,[1,[1,[1,_tf,_1l]],_1l],_])),_th=B(_tc(_te[2],_));return [1,_tg,_th];}},_ti=B((function(_tj,_tk,_){var _tl=_t9(toJSStr(E(_tj))),_tm=B(A(_qY,[_S,_6R,_rS,[1,[1,[1,_tl,_1l]],_1l],_])),_tn=B(_tc(_tk,_));return [1,_tm,_tn];})(_rz,_rL,_)),_to=B(A(_qY,[_S,_6R,_rR,[1,[1,[1,_tb,_ti]],_1l],_])),_tp=E(_pR),_tq=_tp(E(_to),_t7),_tr=E(_t6),_ts=_tr[8],_tt=B(_sU(_tr[2],_1l));if(!_tt[0]){return _a;}else{var _tu=E(_tt[1]),_tv=E(_tu[1]),_tw=E(_tu[2]),_tx=E(_tv[1]),_ty=B(_rh(_tx*25/900,_)),_tz=_ty,_tA=E(_tv[2]),_tB=B(_rh(_tA*25/900,_)),_tC=_tB,_tD=E(_tw[1]),_tE=B(_rh(_tD*25/900,_)),_tF=_tE,_tG=E(_tw[2]),_tH=B(_rh(_tG*25/900,_)),_tI=_tH,_tJ=E(_tr[7]),_tK=function(_tL){var _tM=B(_rh(_tL,_)),_tN=_tM,_tO=function(_tP){var _tQ=rintDouble(_tP*5.8333333333333334e-2*B(_b7(_ts,0))),_tR=B(_rV(_tQ)),_tS=_tR[1],_tT=_tR[2],_tU=function(_tV){var _tW=B(_rh(_tV,_)),_tX=B(_rb(_tz,[1,_tC,[1,_tF,[1,_tI,[1,_tN,[1,_tW,_1l]]]]],_)),_tY=B(A(_qY,[_S,_6R,_rR,[1,new T(function(){return B(_op(_tX));}),_1l],_])),_tZ=B(A(_qY,[_S,_6R,_rQ,[1,_sg,[1,new T(function(){return B(_rt(_se,_tu[3]));}),_1l]],_])),_u0=B(A(_rP,[_])),_u1=B(A(_qY,[_S,_6R,_rT,[1,_sf,[1,[1,[1,_u0,_1l]],_1l]],_])),_u2=B(A(_qY,[_S,_6R,_pM,[1,[1,[1,_tZ,_1l]],_1l],_])),_u3=E(_tY),_u4=_tp(E(_u2),_u3),_u5=E(_u1),_u6=_tp(_u5,_u3),_u7=new T(function(){return B(A(_t5,[_tu]));}),_u8=B(A(_ss,[_6S,_S,_pL,_u5,_rx,function(_u9){return E(_u7);},_])),_ua=new T(function(){return B(A(_t4,[_tZ,_tu]));}),_ub=B(A(_ss,[_6S,_S,_o,_tZ,_rw,function(_uc){return E(_ua);},_])),_ud=_tp(_u3,_t7),_ue=function(_uf,_){var _ug=E(_uf);if(!_ug[0]){return _1l;}else{var _uh=E(_ug[1]),_ui=E(_uh[1]),_uj=E(_uh[2]),_uk=E(_ui[1]),_ul=B(_rh(_uk*25/900,_)),_um=_ul,_un=E(_ui[2]),_uo=B(_rh(_un*25/900,_)),_up=_uo,_uq=E(_uj[1]),_ur=B(_rh(_uq*25/900,_)),_us=_ur,_ut=E(_uj[2]),_uu=B(_rh(_ut*25/900,_)),_uv=_uu,_uw=function(_ux){var _uy=B(_rh(_ux,_)),_uz=_uy,_uA=function(_uB){var _uC=rintDouble(_uB*5.8333333333333334e-2*B(_b7(_ts,0))),_uD=B(_rV(_uC)),_uE=_uD[1],_uF=_uD[2],_uG=function(_uH){var _uI=B(_rh(_uH,_)),_uJ=B(_rb(_um,[1,_up,[1,_us,[1,_uv,[1,_uz,[1,_uI,_1l]]]]],_)),_uK=B(A(_qY,[_S,_6R,_rR,[1,new T(function(){return B(_op(_uJ));}),_1l],_])),_uL=B(A(_qY,[_S,_6R,_rQ,[1,_sg,[1,new T(function(){return B(_rt(_se,_uh[3]));}),_1l]],_])),_uM=B(A(_rP,[_])),_uN=B(A(_qY,[_S,_6R,_rT,[1,_sf,[1,[1,[1,_uM,_1l]],_1l]],_])),_uO=B(A(_qY,[_S,_6R,_pM,[1,[1,[1,_uL,_1l]],_1l],_])),_uP=E(_uK),_uQ=_tp(E(_uO),_uP),_uR=E(_uN),_uS=_tp(_uR,_uP),_uT=new T(function(){return B(A(_t5,[_uh]));}),_uU=B(A(_ss,[_6S,_S,_pL,_uR,_rx,function(_uV){return E(_uT);},_])),_uW=new T(function(){return B(A(_t4,[_uL,_uh]));}),_uX=B(A(_ss,[_6S,_S,_o,_uL,_rw,function(_uY){return E(_uW);},_])),_uZ=_tp(_uP,_t7),_v0=B(_ue(_ug[2],_));return [1,_a,_v0];};if(_uF>=0){return new F(function(){return _uG(B(_rY(B(_sZ(_uE,_uF)))));});}else{var _v1=hs_uncheckedIShiftRA64(B(_sb(_uE)), -_uF);return new F(function(){return _uG(B(_rY(B(_s1(_v1)))));});}};if(_uk!=_uk){return new F(function(){return _uA(B(_rl(_tJ,_uk,_uq)));});}else{return new F(function(){return _uA(B(_rl(_tJ,_un,_ut)));});}};if(_uk!=_uk){return new F(function(){return _uw(B(_rl(_tJ,_uk,_uq)));});}else{return new F(function(){return _uw(B(_rl(_tJ,_un,_ut)));});}}},_v2=B(_ue(_tt[2],_));return [1,_a,_v2];};if(_tT>=0){return new F(function(){return _tU(B(_rY(B(_sZ(_tS,_tT)))));});}else{var _v3=hs_uncheckedIShiftRA64(B(_sb(_tS)), -_tT);return new F(function(){return _tU(B(_rY(B(_s1(_v3)))));});}};if(_tx!=_tx){return new F(function(){return _tO(B(_rl(_tJ,_tx,_tD)));});}else{return new F(function(){return _tO(B(_rl(_tJ,_tA,_tG)));});}};if(_tx!=_tx){var _v4=B(_tK(B(_rl(_tJ,_tx,_tD))));return _a;}else{var _v5=B(_tK(B(_rl(_tJ,_tA,_tG))));return _a;}}},_v6=function(_){return _a;},_v7=(function(ctx){ctx.restore();}),_v8=(function(ctx){ctx.save();}),_v9=(function(ctx,x,y){ctx.scale(x,y);}),_va=function(_vb,_vc,_vd,_ve,_){var _vf=E(_v8)(_ve),_vg=E(_v9)(_ve,E(_vb),E(_vc)),_vh=B(A(_vd,[_ve,_])),_vi=E(_v7)(_ve);return new F(function(){return _v6(_);});},_vj=(function(ctx){ctx.beginPath();}),_vk=(function(ctx){ctx.stroke();}),_vl=function(_vm,_vn,_){var _vo=E(_vj)(_vn),_vp=B(A(_vm,[_vn,_])),_vq=E(_vk)(_vn);return new F(function(){return _v6(_);});},_vr=(function(ctx,i,x,y){ctx.drawImage(i,x,y);}),_vs=function(_vt,_vu,_vv,_vw,_){var _vx=E(_vr)(_vw,_vt,_vu,_vv);return new F(function(){return _v6(_);});},_vy=",",_vz="[",_vA="]",_vB="{",_vC="}",_vD=":",_vE="\"",_vF="true",_vG="false",_vH="null",_vI=new T(function(){return JSON.stringify;}),_vJ=function(_vK,_vL){var _vM=E(_vL);switch(_vM[0]){case 0:return [0,new T(function(){return jsShow(_vM[1]);}),_vK];case 1:return [0,new T(function(){var _vN=E(_vI)(_vM[1]);return String(_vN);}),_vK];case 2:return (!E(_vM[1]))?[0,_vG,_vK]:[0,_vF,_vK];case 3:var _vO=E(_vM[1]);if(!_vO[0]){return [0,_vz,[1,_vA,_vK]];}else{var _vP=new T(function(){var _vQ=new T(function(){var _vR=function(_vS){var _vT=E(_vS);if(!_vT[0]){return [1,_vA,_vK];}else{var _vU=new T(function(){var _vV=B(_vJ(new T(function(){return B(_vR(_vT[2]));}),_vT[1]));return [1,_vV[1],_vV[2]];});return [1,_vy,_vU];}};return B(_vR(_vO[2]));}),_vW=B(_vJ(_vQ,_vO[1]));return [1,_vW[1],_vW[2]];});return [0,_vz,_vP];}break;case 4:var _vX=E(_vM[1]);if(!_vX[0]){return [0,_vB,[1,_vC,_vK]];}else{var _vY=E(_vX[1]),_vZ=new T(function(){var _w0=new T(function(){var _w1=function(_w2){var _w3=E(_w2);if(!_w3[0]){return [1,_vC,_vK];}else{var _w4=E(_w3[1]),_w5=new T(function(){var _w6=B(_vJ(new T(function(){return B(_w1(_w3[2]));}),_w4[2]));return [1,_w6[1],_w6[2]];});return [1,_vy,[1,_vE,[1,_w4[1],[1,_vE,[1,_vD,_w5]]]]];}};return B(_w1(_vX[2]));}),_w7=B(_vJ(_w0,_vY[2]));return [1,_w7[1],_w7[2]];});return [0,_vB,[1,new T(function(){var _w8=E(_vI)(E(_vY[1]));return String(_w8);}),[1,_vD,_vZ]]];}break;default:return [0,_vH,_vK];}},_w9=new T(function(){return toJSStr(_1l);}),_wa=function(_wb){var _wc=B(_vJ(_1l,_wb)),_wd=jsCat([1,_wc[1],_wc[2]],E(_w9));return E(_wd);},_we=function(_wf){while(1){var _wg=E(_wf);if(!_wg[0]){_wf=[1,I_fromInt(_wg[1])];continue;}else{return new F(function(){return I_toString(_wg[1]);});}}},_wh=function(_wi,_wj){return new F(function(){return _16(fromJSStr(B(_we(_wi))),_wj);});},_wk=function(_wl,_wm){var _wn=E(_wl);if(!_wn[0]){var _wo=_wn[1],_wp=E(_wm);return (_wp[0]==0)?_wo<_wp[1]:I_compareInt(_wp[1],_wo)>0;}else{var _wq=_wn[1],_wr=E(_wm);return (_wr[0]==0)?I_compareInt(_wq,_wr[1])<0:I_compare(_wq,_wr[1])<0;}},_ws=[0,0],_wt=function(_wu,_wv,_ww){if(_wu<=6){return new F(function(){return _wh(_wv,_ww);});}else{if(!B(_wk(_wv,_ws))){return new F(function(){return _wh(_wv,_ww);});}else{return [1,_1f,new T(function(){return B(_16(fromJSStr(B(_we(_wv))),[1,_1e,_ww]));})];}}},_wx=0,_wy=1,_wz=function(_wA){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_wA));}))));});},_wB=new T(function(){return B(_wz("ww_syKY MouseState"));}),_wC=function(_wD){var _wE=E(_wD);if(!_wE[0]){return [0];}else{return new F(function(){return _16(_wE[1],new T(function(){return B(_wC(_wE[2]));},1));});}},_wF=new T(function(){return B(unCStr("\r\n"));}),_wG=new T(function(){return B(_16(_wF,_wF));}),_wH=function(_wI,_wJ){var _wK=E(_wJ);return (_wK[0]==0)?[0]:[1,_wI,[1,_wK[1],new T(function(){return B(_wH(_wI,_wK[2]));})]];},_wL=new T(function(){return B(unCStr("printf: formatting string ended prematurely"));}),_wM=new T(function(){return B(err(_wL));}),_wN=function(_wO,_wP){var _wQ=E(_wP);return (_wQ[0]==0)?E(_wM):[0,_1l,_wQ[1],_wQ[2]];},_wR=new T(function(){return B(unCStr("!!: negative index"));}),_wS=new T(function(){return B(unCStr("Prelude."));}),_wT=new T(function(){return B(_16(_wS,_wR));}),_wU=new T(function(){return B(err(_wT));}),_wV=new T(function(){return B(unCStr("!!: index too large"));}),_wW=new T(function(){return B(_16(_wS,_wV));}),_wX=new T(function(){return B(err(_wW));}),_wY=function(_wZ,_x0){while(1){var _x1=E(_wZ);if(!_x1[0]){return E(_wX);}else{var _x2=E(_x0);if(!_x2){return E(_x1[1]);}else{_wZ=_x1[2];_x0=_x2-1|0;continue;}}}},_x3=function(_x4,_x5){if(_x5>=0){return new F(function(){return _wY(_x4,_x5);});}else{return E(_wU);}},_x6=new T(function(){return B(unCStr("ACK"));}),_x7=new T(function(){return B(unCStr("BEL"));}),_x8=new T(function(){return B(unCStr("BS"));}),_x9=new T(function(){return B(unCStr("SP"));}),_xa=[1,_x9,_1l],_xb=new T(function(){return B(unCStr("US"));}),_xc=[1,_xb,_xa],_xd=new T(function(){return B(unCStr("RS"));}),_xe=[1,_xd,_xc],_xf=new T(function(){return B(unCStr("GS"));}),_xg=[1,_xf,_xe],_xh=new T(function(){return B(unCStr("FS"));}),_xi=[1,_xh,_xg],_xj=new T(function(){return B(unCStr("ESC"));}),_xk=[1,_xj,_xi],_xl=new T(function(){return B(unCStr("SUB"));}),_xm=[1,_xl,_xk],_xn=new T(function(){return B(unCStr("EM"));}),_xo=[1,_xn,_xm],_xp=new T(function(){return B(unCStr("CAN"));}),_xq=[1,_xp,_xo],_xr=new T(function(){return B(unCStr("ETB"));}),_xs=[1,_xr,_xq],_xt=new T(function(){return B(unCStr("SYN"));}),_xu=[1,_xt,_xs],_xv=new T(function(){return B(unCStr("NAK"));}),_xw=[1,_xv,_xu],_xx=new T(function(){return B(unCStr("DC4"));}),_xy=[1,_xx,_xw],_xz=new T(function(){return B(unCStr("DC3"));}),_xA=[1,_xz,_xy],_xB=new T(function(){return B(unCStr("DC2"));}),_xC=[1,_xB,_xA],_xD=new T(function(){return B(unCStr("DC1"));}),_xE=[1,_xD,_xC],_xF=new T(function(){return B(unCStr("DLE"));}),_xG=[1,_xF,_xE],_xH=new T(function(){return B(unCStr("SI"));}),_xI=[1,_xH,_xG],_xJ=new T(function(){return B(unCStr("SO"));}),_xK=[1,_xJ,_xI],_xL=new T(function(){return B(unCStr("CR"));}),_xM=[1,_xL,_xK],_xN=new T(function(){return B(unCStr("FF"));}),_xO=[1,_xN,_xM],_xP=new T(function(){return B(unCStr("VT"));}),_xQ=[1,_xP,_xO],_xR=new T(function(){return B(unCStr("LF"));}),_xS=[1,_xR,_xQ],_xT=new T(function(){return B(unCStr("HT"));}),_xU=[1,_xT,_xS],_xV=[1,_x8,_xU],_xW=[1,_x7,_xV],_xX=[1,_x6,_xW],_xY=new T(function(){return B(unCStr("ENQ"));}),_xZ=[1,_xY,_xX],_y0=new T(function(){return B(unCStr("EOT"));}),_y1=[1,_y0,_xZ],_y2=new T(function(){return B(unCStr("ETX"));}),_y3=[1,_y2,_y1],_y4=new T(function(){return B(unCStr("STX"));}),_y5=[1,_y4,_y3],_y6=new T(function(){return B(unCStr("SOH"));}),_y7=[1,_y6,_y5],_y8=new T(function(){return B(unCStr("NUL"));}),_y9=[1,_y8,_y7],_ya=92,_yb=new T(function(){return B(unCStr("\\DEL"));}),_yc=new T(function(){return B(unCStr("\\a"));}),_yd=new T(function(){return B(unCStr("\\\\"));}),_ye=new T(function(){return B(unCStr("\\SO"));}),_yf=new T(function(){return B(unCStr("\\r"));}),_yg=new T(function(){return B(unCStr("\\f"));}),_yh=new T(function(){return B(unCStr("\\v"));}),_yi=new T(function(){return B(unCStr("\\n"));}),_yj=new T(function(){return B(unCStr("\\t"));}),_yk=new T(function(){return B(unCStr("\\b"));}),_yl=function(_ym,_yn){if(_ym<=127){var _yo=E(_ym);switch(_yo){case 92:return new F(function(){return _16(_yd,_yn);});break;case 127:return new F(function(){return _16(_yb,_yn);});break;default:if(_yo<32){var _yp=E(_yo);switch(_yp){case 7:return new F(function(){return _16(_yc,_yn);});break;case 8:return new F(function(){return _16(_yk,_yn);});break;case 9:return new F(function(){return _16(_yj,_yn);});break;case 10:return new F(function(){return _16(_yi,_yn);});break;case 11:return new F(function(){return _16(_yh,_yn);});break;case 12:return new F(function(){return _16(_yg,_yn);});break;case 13:return new F(function(){return _16(_yf,_yn);});break;case 14:return new F(function(){return _16(_ye,new T(function(){var _yq=E(_yn);if(!_yq[0]){return [0];}else{if(E(_yq[1])==72){return B(unAppCStr("\\&",_yq));}else{return E(_yq);}}},1));});break;default:return new F(function(){return _16([1,_ya,new T(function(){return B(_x3(_y9,_yp));})],_yn);});}}else{return [1,_yo,_yn];}}}else{var _yr=new T(function(){var _ys=jsShowI(_ym);return B(_16(fromJSStr(_ys),new T(function(){var _yt=E(_yn);if(!_yt[0]){return [0];}else{var _yu=E(_yt[1]);if(_yu<48){return E(_yt);}else{if(_yu>57){return E(_yt);}else{return B(unAppCStr("\\&",_yt));}}}},1)));});return [1,_ya,_yr];}},_yv=39,_yw=[1,_yv,_1l],_yx=new T(function(){return B(unCStr("\'\\\'\'"));}),_yy=new T(function(){return B(_16(_yx,_1l));}),_yz=function(_yA){var _yB=new T(function(){var _yC=new T(function(){var _yD=E(_yA);if(_yD==39){return E(_yy);}else{return [1,_yv,new T(function(){return B(_yl(_yD,_yw));})];}});return B(unAppCStr("bad formatting char ",_yC));});return new F(function(){return err(B(unAppCStr("printf: ",_yB)));});},_yE=new T(function(){return B(unCStr("-"));}),_yF=new T(function(){return B(unCStr("printf: internal error: impossible dfmt"));}),_yG=new T(function(){return B(err(_yF));}),_yH=function(_yI){var _yJ=E(_yI);return new F(function(){return Math.log(_yJ+(_yJ+1)*Math.sqrt((_yJ-1)/(_yJ+1)));});},_yK=function(_yL){var _yM=E(_yL);return new F(function(){return Math.log(_yM+Math.sqrt(1+_yM*_yM));});},_yN=function(_yO){var _yP=E(_yO);return 0.5*Math.log((1+_yP)/(1-_yP));},_yQ=function(_yR,_yS){return Math.log(E(_yS))/Math.log(E(_yR));},_yT=3.141592653589793,_yU=[0,1],_yV=function(_yW,_yX){var _yY=E(_yW);if(!_yY[0]){var _yZ=_yY[1],_z0=E(_yX);if(!_z0[0]){var _z1=_z0[1];return (_yZ!=_z1)?(_yZ>_z1)?2:0:1;}else{var _z2=I_compareInt(_z0[1],_yZ);return (_z2<=0)?(_z2>=0)?1:2:0;}}else{var _z3=_yY[1],_z4=E(_yX);if(!_z4[0]){var _z5=I_compareInt(_z3,_z4[1]);return (_z5>=0)?(_z5<=0)?1:2:0;}else{var _z6=I_compare(_z3,_z4[1]);return (_z6>=0)?(_z6<=0)?1:2:0;}}},_z7=new T(function(){return B(unCStr("GHC.Exception"));}),_z8=new T(function(){return B(unCStr("base"));}),_z9=new T(function(){return B(unCStr("ArithException"));}),_za=new T(function(){var _zb=hs_wordToWord64(4194982440),_zc=hs_wordToWord64(3110813675);return [0,_zb,_zc,[0,_zb,_zc,_z8,_z7,_z9],_1l,_1l];}),_zd=function(_ze){return E(_za);},_zf=function(_zg){var _zh=E(_zg);return new F(function(){return _5g(B(_5e(_zh[1])),_zd,_zh[2]);});},_zi=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_zj=new T(function(){return B(unCStr("denormal"));}),_zk=new T(function(){return B(unCStr("divide by zero"));}),_zl=new T(function(){return B(unCStr("loss of precision"));}),_zm=new T(function(){return B(unCStr("arithmetic underflow"));}),_zn=new T(function(){return B(unCStr("arithmetic overflow"));}),_zo=function(_zp,_zq){switch(E(_zp)){case 0:return new F(function(){return _16(_zn,_zq);});break;case 1:return new F(function(){return _16(_zm,_zq);});break;case 2:return new F(function(){return _16(_zl,_zq);});break;case 3:return new F(function(){return _16(_zk,_zq);});break;case 4:return new F(function(){return _16(_zj,_zq);});break;default:return new F(function(){return _16(_zi,_zq);});}},_zr=function(_zs){return new F(function(){return _zo(_zs,_1l);});},_zt=function(_zu,_zv,_zw){return new F(function(){return _zo(_zv,_zw);});},_zx=function(_zy,_zz){return new F(function(){return _6r(_zo,_zy,_zz);});},_zA=[0,_zt,_zr,_zx],_zB=new T(function(){return [0,_zd,_zA,_zC,_zf,_zr];}),_zC=function(_7s){return [0,_zB,_7s];},_zD=3,_zE=new T(function(){return B(_zC(_zD));}),_zF=new T(function(){return die(_zE);}),_zG=function(_zH,_zI){var _zJ=E(_zH);return (_zJ[0]==0)?_zJ[1]*Math.pow(2,_zI):I_toNumber(_zJ[1])*Math.pow(2,_zI);},_zK=function(_zL,_zM){var _zN=E(_zL);if(!_zN[0]){var _zO=_zN[1],_zP=E(_zM);return (_zP[0]==0)?_zO==_zP[1]:(I_compareInt(_zP[1],_zO)==0)?true:false;}else{var _zQ=_zN[1],_zR=E(_zM);return (_zR[0]==0)?(I_compareInt(_zQ,_zR[1])==0)?true:false:(I_compare(_zQ,_zR[1])==0)?true:false;}},_zS=function(_zT,_zU){while(1){var _zV=E(_zT);if(!_zV[0]){var _zW=E(_zV[1]);if(_zW==(-2147483648)){_zT=[1,I_fromInt(-2147483648)];continue;}else{var _zX=E(_zU);if(!_zX[0]){var _zY=_zX[1];return [0,[0,quot(_zW,_zY)],[0,_zW%_zY]];}else{_zT=[1,I_fromInt(_zW)];_zU=_zX;continue;}}}else{var _zZ=E(_zU);if(!_zZ[0]){_zT=_zV;_zU=[1,I_fromInt(_zZ[1])];continue;}else{var _A0=I_quotRem(_zV[1],_zZ[1]);return [0,[1,_A0[1]],[1,_A0[2]]];}}}},_A1=[0,0],_A2=function(_A3,_A4,_A5){if(!B(_zK(_A5,_A1))){var _A6=B(_zS(_A4,_A5)),_A7=_A6[1];switch(B(_yV(B(_sZ(_A6[2],1)),_A5))){case 0:return new F(function(){return _zG(_A7,_A3);});break;case 1:if(!(B(_cK(_A7))&1)){return new F(function(){return _zG(_A7,_A3);});}else{return new F(function(){return _zG(B(_aS(_A7,_yU)),_A3);});}break;default:return new F(function(){return _zG(B(_aS(_A7,_yU)),_A3);});}}else{return E(_zF);}},_A8=function(_A9,_Aa){var _Ab=E(_A9);if(!_Ab[0]){var _Ac=_Ab[1],_Ad=E(_Aa);return (_Ad[0]==0)?_Ac>_Ad[1]:I_compareInt(_Ad[1],_Ac)<0;}else{var _Ae=_Ab[1],_Af=E(_Aa);return (_Af[0]==0)?I_compareInt(_Ae,_Af[1])>0:I_compare(_Ae,_Af[1])>0;}},_Ag=function(_Ah){var _Ai=_aQ,_Aj=0;while(1){if(!B(_wk(_Ai,_Ah))){if(!B(_A8(_Ai,_Ah))){if(!B(_zK(_Ai,_Ah))){return new F(function(){return _7P("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_Aj);}}else{return _Aj-1|0;}}else{var _Ak=B(_sZ(_Ai,1)),_Al=_Aj+1|0;_Ai=_Ak;_Aj=_Al;continue;}}},_Am=function(_An){var _Ao=E(_An);if(!_Ao[0]){var _Ap=_Ao[1]>>>0;if(!_Ap){return -1;}else{var _Aq=1,_Ar=0;while(1){if(_Aq>=_Ap){if(_Aq<=_Ap){if(_Aq!=_Ap){return new F(function(){return _7P("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_Ar);}}else{return _Ar-1|0;}}else{var _As=imul(_Aq,2)>>>0,_At=_Ar+1|0;_Aq=_As;_Ar=_At;continue;}}}}else{return new F(function(){return _Ag(_Ao);});}},_Au=function(_Av){var _Aw=E(_Av);if(!_Aw[0]){var _Ax=_Aw[1]>>>0;if(!_Ax){return [0,-1,0];}else{var _Ay=function(_Az,_AA){while(1){if(_Az>=_Ax){if(_Az<=_Ax){if(_Az!=_Ax){return new F(function(){return _7P("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_AA);}}else{return _AA-1|0;}}else{var _AB=imul(_Az,2)>>>0,_AC=_AA+1|0;_Az=_AB;_AA=_AC;continue;}}};return [0,B(_Ay(1,0)),(_Ax&_Ax-1>>>0)>>>0&4294967295];}}else{var _AD=B(_Am(_Aw)),_AE=_AD>>>0;if(!_AE){var _AF=E(_AD);return (_AF==(-2))?[0,-2,0]:[0,_AF,1];}else{var _AG=function(_AH,_AI){while(1){if(_AH>=_AE){if(_AH<=_AE){if(_AH!=_AE){return new F(function(){return _7P("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_AI);}}else{return _AI-1|0;}}else{var _AJ=imul(_AH,2)>>>0,_AK=_AI+1|0;_AH=_AJ;_AI=_AK;continue;}}},_AL=B(_AG(1,0));return ((_AL+_AL|0)!=_AD)?[0,_AD,1]:[0,_AD,0];}}},_AM=function(_AN,_AO){while(1){var _AP=E(_AN);if(!_AP[0]){var _AQ=_AP[1],_AR=E(_AO);if(!_AR[0]){return [0,(_AQ>>>0&_AR[1]>>>0)>>>0&4294967295];}else{_AN=[1,I_fromInt(_AQ)];_AO=_AR;continue;}}else{var _AS=E(_AO);if(!_AS[0]){_AN=_AP;_AO=[1,I_fromInt(_AS[1])];continue;}else{return [1,I_and(_AP[1],_AS[1])];}}}},_AT=function(_AU,_AV){while(1){var _AW=E(_AU);if(!_AW[0]){var _AX=_AW[1],_AY=E(_AV);if(!_AY[0]){var _AZ=_AY[1],_B0=subC(_AX,_AZ);if(!E(_B0[2])){return [0,_B0[1]];}else{_AU=[1,I_fromInt(_AX)];_AV=[1,I_fromInt(_AZ)];continue;}}else{_AU=[1,I_fromInt(_AX)];_AV=_AY;continue;}}else{var _B1=E(_AV);if(!_B1[0]){_AU=_AW;_AV=[1,I_fromInt(_B1[1])];continue;}else{return [1,I_sub(_AW[1],_B1[1])];}}}},_B2=[0,2],_B3=function(_B4,_B5){var _B6=E(_B4);if(!_B6[0]){var _B7=(_B6[1]>>>0&(2<<_B5>>>0)-1>>>0)>>>0,_B8=1<<_B5>>>0;return (_B8<=_B7)?(_B8>=_B7)?1:2:0;}else{var _B9=B(_AM(_B6,B(_AT(B(_sZ(_B2,_B5)),_aQ)))),_Ba=B(_sZ(_aQ,_B5));return (!B(_A8(_Ba,_B9)))?(!B(_wk(_Ba,_B9)))?1:2:0;}},_Bb=function(_Bc,_Bd){while(1){var _Be=E(_Bc);if(!_Be[0]){_Bc=[1,I_fromInt(_Be[1])];continue;}else{return [1,I_shiftRight(_Be[1],_Bd)];}}},_Bf=function(_Bg,_Bh,_Bi,_Bj){var _Bk=B(_Au(_Bj)),_Bl=_Bk[1];if(!E(_Bk[2])){var _Bm=B(_Am(_Bi));if(_Bm<((_Bl+_Bg|0)-1|0)){var _Bn=_Bl+(_Bg-_Bh|0)|0;if(_Bn>0){if(_Bn>_Bm){if(_Bn<=(_Bm+1|0)){if(!E(B(_Au(_Bi))[2])){return 0;}else{return new F(function(){return _zG(_yU,_Bg-_Bh|0);});}}else{return 0;}}else{var _Bo=B(_Bb(_Bi,_Bn));switch(B(_B3(_Bi,_Bn-1|0))){case 0:return new F(function(){return _zG(_Bo,_Bg-_Bh|0);});break;case 1:if(!(B(_cK(_Bo))&1)){return new F(function(){return _zG(_Bo,_Bg-_Bh|0);});}else{return new F(function(){return _zG(B(_aS(_Bo,_yU)),_Bg-_Bh|0);});}break;default:return new F(function(){return _zG(B(_aS(_Bo,_yU)),_Bg-_Bh|0);});}}}else{return new F(function(){return _zG(_Bi,(_Bg-_Bh|0)-_Bn|0);});}}else{if(_Bm>=_Bh){var _Bp=B(_Bb(_Bi,(_Bm+1|0)-_Bh|0));switch(B(_B3(_Bi,_Bm-_Bh|0))){case 0:return new F(function(){return _zG(_Bp,((_Bm-_Bl|0)+1|0)-_Bh|0);});break;case 2:return new F(function(){return _zG(B(_aS(_Bp,_yU)),((_Bm-_Bl|0)+1|0)-_Bh|0);});break;default:if(!(B(_cK(_Bp))&1)){return new F(function(){return _zG(_Bp,((_Bm-_Bl|0)+1|0)-_Bh|0);});}else{return new F(function(){return _zG(B(_aS(_Bp,_yU)),((_Bm-_Bl|0)+1|0)-_Bh|0);});}}}else{return new F(function(){return _zG(_Bi, -_Bl);});}}}else{var _Bq=B(_Am(_Bi))-_Bl|0,_Br=function(_Bs){var _Bt=function(_Bu,_Bv){if(!B(_cN(B(_sZ(_Bv,_Bh)),_Bu))){return new F(function(){return _A2(_Bs-_Bh|0,_Bu,_Bv);});}else{return new F(function(){return _A2((_Bs-_Bh|0)+1|0,_Bu,B(_sZ(_Bv,1)));});}};if(_Bs>=_Bh){if(_Bs!=_Bh){return new F(function(){return _Bt(_Bi,new T(function(){return B(_sZ(_Bj,_Bs-_Bh|0));}));});}else{return new F(function(){return _Bt(_Bi,_Bj);});}}else{return new F(function(){return _Bt(new T(function(){return B(_sZ(_Bi,_Bh-_Bs|0));}),_Bj);});}};if(_Bg>_Bq){return new F(function(){return _Br(_Bg);});}else{return new F(function(){return _Br(_Bq);});}}},_Bw=new T(function(){return 0/0;}),_Bx=new T(function(){return -1/0;}),_By=new T(function(){return 1/0;}),_Bz=0,_BA=function(_BB,_BC){if(!B(_zK(_BC,_A1))){if(!B(_zK(_BB,_A1))){if(!B(_wk(_BB,_A1))){return new F(function(){return _Bf(-1021,53,_BB,_BC);});}else{return  -B(_Bf(-1021,53,B(_b2(_BB)),_BC));}}else{return E(_Bz);}}else{return (!B(_zK(_BB,_A1)))?(!B(_wk(_BB,_A1)))?E(_By):E(_Bx):E(_Bw);}},_BD=function(_BE){var _BF=E(_BE);return new F(function(){return _BA(_BF[1],_BF[2]);});},_BG=function(_BH){return 1/E(_BH);},_BI=function(_BJ){var _BK=E(_BJ),_BL=E(_BK);return (_BL==0)?E(_Bz):(_BL<=0)? -_BL:E(_BK);},_BM=function(_BN){return new F(function(){return _rY(_BN);});},_BO=1,_BP=-1,_BQ=function(_BR){var _BS=E(_BR);return (_BS<=0)?(_BS>=0)?E(_BS):E(_BP):E(_BO);},_BT=function(_BU,_BV){return E(_BU)-E(_BV);},_BW=function(_BX){return  -E(_BX);},_BY=function(_BZ,_C0){return E(_BZ)+E(_C0);},_C1=function(_C2,_C3){return E(_C2)*E(_C3);},_C4=[0,_BY,_BT,_C1,_BW,_BI,_BQ,_BM],_C5=function(_C6,_C7){return E(_C6)/E(_C7);},_C8=[0,_C4,_C5,_BG,_BD],_C9=function(_Ca){return new F(function(){return Math.acos(E(_Ca));});},_Cb=function(_Cc){return new F(function(){return Math.asin(E(_Cc));});},_Cd=function(_Ce){return new F(function(){return Math.atan(E(_Ce));});},_Cf=function(_Cg){return new F(function(){return Math.cos(E(_Cg));});},_Ch=function(_Ci){return new F(function(){return cosh(E(_Ci));});},_Cj=function(_Ck){return new F(function(){return Math.exp(E(_Ck));});},_Cl=function(_Cm){return new F(function(){return Math.log(E(_Cm));});},_Cn=function(_Co,_Cp){return new F(function(){return Math.pow(E(_Co),E(_Cp));});},_Cq=function(_Cr){return new F(function(){return Math.sin(E(_Cr));});},_Cs=function(_Ct){return new F(function(){return sinh(E(_Ct));});},_Cu=function(_Cv){return new F(function(){return Math.sqrt(E(_Cv));});},_Cw=function(_Cx){return new F(function(){return Math.tan(E(_Cx));});},_Cy=function(_Cz){return new F(function(){return tanh(E(_Cz));});},_CA=[0,_C8,_yT,_Cj,_Cl,_Cu,_Cn,_yQ,_Cq,_Cf,_Cw,_Cb,_C9,_Cd,_Cs,_Ch,_Cy,_yK,_yH,_yN],_CB=function(_CC,_CD){if(_CD<=0){var _CE=function(_CF){var _CG=function(_CH){var _CI=function(_CJ){var _CK=function(_CL){var _CM=isDoubleNegativeZero(_CD),_CN=_CM,_CO=function(_CP){var _CQ=E(_CC);if(!_CQ){return (_CD>=0)?(E(_CN)==0)?E(_CD):3.141592653589793:3.141592653589793;}else{var _CR=E(_CD);return (_CR==0)?E(_CQ):_CR+_CQ;}};if(!E(_CN)){return new F(function(){return _CO(_);});}else{var _CS=E(_CC),_CT=isDoubleNegativeZero(_CS);if(!E(_CT)){return new F(function(){return _CO(_);});}else{return  -B(_CB( -_CS,_CD));}}};if(_CD>=0){return new F(function(){return _CK(_);});}else{var _CU=E(_CC),_CV=isDoubleNegativeZero(_CU);if(!E(_CV)){return new F(function(){return _CK(_);});}else{return  -B(_CB( -_CU,_CD));}}};if(_CD>0){return new F(function(){return _CI(_);});}else{var _CW=E(_CC);if(_CW>=0){return new F(function(){return _CI(_);});}else{return  -B(_CB( -_CW,_CD));}}};if(_CD>=0){return new F(function(){return _CG(_);});}else{var _CX=E(_CC);if(_CX<=0){return new F(function(){return _CG(_);});}else{return 3.141592653589793+Math.atan(_CX/_CD);}}};if(!E(_CD)){if(E(_CC)<=0){return new F(function(){return _CE(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _CE(_);});}}else{return new F(function(){return Math.atan(E(_CC)/_CD);});}},_CY=function(_CZ,_D0){return new F(function(){return _CB(_CZ,E(_D0));});},_D1=function(_D2){var _D3=B(_rV(E(_D2)));return [0,_D3[1],_D3[2]];},_D4=function(_D5,_D6){return new F(function(){return _zG(_D5,E(_D6));});},_D7=function(_D8){var _D9=B(_rV(_D8));return (!B(_zK(_D9[1],_A1)))?_D9[2]+53|0:0;},_Da=function(_Db){return new F(function(){return _D7(E(_Db));});},_Dc=53,_Dd=function(_De){return E(_Dc);},_Df=[0,2],_Dg=function(_Dh){return E(_Df);},_Di=1024,_Dj=-1021,_Dk=[0,_Dj,_Di],_Dl=function(_Dm){return E(_Dk);},_Dn=function(_Do){var _Dp=isDoubleDenormalized(E(_Do));return (E(_Dp)==0)?false:true;},_Dq=function(_Dr){return true;},_Ds=function(_Dt){var _Du=isDoubleInfinite(E(_Dt));return (E(_Du)==0)?false:true;},_Dv=function(_Dw){var _Dx=isDoubleNaN(E(_Dw));return (E(_Dx)==0)?false:true;},_Dy=function(_Dz){var _DA=isDoubleNegativeZero(E(_Dz));return (E(_DA)==0)?false:true;},_DB=function(_DC,_DD){var _DE=E(_DC);if(!_DE){return E(_DD);}else{var _DF=E(_DD);if(!_DF){return 0;}else{var _DG=isDoubleFinite(_DF);if(!E(_DG)){return E(_DF);}else{var _DH=B(_rV(_DF)),_DI=_DH[1],_DJ=_DH[2];if(2257>_DE){if(-2257>_DE){return new F(function(){return _zG(_DI,_DJ+(-2257)|0);});}else{return new F(function(){return _zG(_DI,_DJ+_DE|0);});}}else{return new F(function(){return _zG(_DI,_DJ+2257|0);});}}}}},_DK=function(_DL,_DM){return new F(function(){return _DB(E(_DL),E(_DM));});},_DN=function(_DO){return new F(function(){return _zG(B(_rV(E(_DO)))[1],-53);});},_DP=function(_DQ,_DR){return (E(_DQ)!=E(_DR))?true:false;},_DS=function(_DT,_DU){return E(_DT)==E(_DU);},_DV=[0,_DS,_DP],_DW=function(_DX,_DY){return E(_DX)<E(_DY);},_DZ=function(_E0,_E1){return E(_E0)<=E(_E1);},_E2=function(_E3,_E4){return E(_E3)>E(_E4);},_E5=function(_E6,_E7){return E(_E6)>=E(_E7);},_E8=function(_E9,_Ea){var _Eb=E(_E9),_Ec=E(_Ea);return (_Eb>=_Ec)?(_Eb!=_Ec)?2:1:0;},_Ed=function(_Ee,_Ef){var _Eg=E(_Ee),_Eh=E(_Ef);return (_Eg>_Eh)?E(_Eg):E(_Eh);},_Ei=function(_Ej,_Ek){var _El=E(_Ej),_Em=E(_Ek);return (_El>_Em)?E(_Em):E(_El);},_En=[0,_DV,_E8,_DW,_DZ,_E2,_E5,_Ed,_Ei],_Eo=new T(function(){var _Ep=newByteArr(256),_Eq=_Ep,_=_Eq["v"]["i8"][0]=8,_Er=function(_Es,_Et,_Eu,_){while(1){if(_Eu>=256){if(_Es>=256){return E(_);}else{var _Ev=imul(2,_Es)|0,_Ew=_Et+1|0,_Ex=_Es;_Es=_Ev;_Et=_Ew;_Eu=_Ex;continue;}}else{var _=_Eq["v"]["i8"][_Eu]=_Et,_Ex=_Eu+_Es|0;_Eu=_Ex;continue;}}},_=B(_Er(2,0,1,_));return _Eq;}),_Ey=function(_Ez,_EA){while(1){var _EB=B((function(_EC,_ED){var _EE=hs_int64ToInt(_EC),_EF=E(_Eo)["v"]["i8"][(255&_EE>>>0)>>>0&4294967295];if(_ED>_EF){if(_EF>=8){var _EG=hs_uncheckedIShiftRA64(_EC,8),_EH=_ED-8|0;_Ez=_EG;_EA=_EH;return null;}else{return [0,new T(function(){var _EI=hs_uncheckedIShiftRA64(_EC,_EF);return B(_s1(_EI));}),_ED-_EF|0];}}else{return [0,new T(function(){var _EJ=hs_uncheckedIShiftRA64(_EC,_ED);return B(_s1(_EJ));}),0];}})(_Ez,_EA));if(_EB!=null){return _EB;}}},_EK=function(_EL){return I_toInt(_EL)>>>0;},_EM=function(_EN){var _EO=E(_EN);if(!_EO[0]){return _EO[1]>>>0;}else{return new F(function(){return _EK(_EO[1]);});}},_EP=function(_EQ){var _ER=B(_rV(_EQ)),_ES=_ER[1],_ET=_ER[2];if(_ET<0){var _EU=function(_EV){if(!_EV){return [0,E(_ES),B(_sZ(_yU, -_ET))];}else{var _EW=B(_Ey(B(_sb(_ES)), -_ET));return [0,E(_EW[1]),B(_sZ(_yU,_EW[2]))];}};if(!((B(_EM(_ES))&1)>>>0)){return new F(function(){return _EU(1);});}else{return new F(function(){return _EU(0);});}}else{return [0,B(_sZ(_ES,_ET)),_yU];}},_EX=function(_EY){var _EZ=B(_EP(E(_EY)));return [0,E(_EZ[1]),E(_EZ[2])];},_F0=[0,_C4,_En,_EX],_F1=function(_F2){return E(E(_F2)[1]);},_F3=function(_F4){return E(E(_F4)[1]);},_F5=[0,1],_F6=function(_F7,_F8){if(_F7<=_F8){var _F9=function(_Fa){return [1,_Fa,new T(function(){if(_Fa!=_F8){return B(_F9(_Fa+1|0));}else{return [0];}})];};return new F(function(){return _F9(_F7);});}else{return [0];}},_Fb=function(_Fc){return new F(function(){return _F6(E(_Fc),2147483647);});},_Fd=function(_Fe,_Ff,_Fg){if(_Fg<=_Ff){var _Fh=new T(function(){var _Fi=_Ff-_Fe|0,_Fj=function(_Fk){return (_Fk>=(_Fg-_Fi|0))?[1,_Fk,new T(function(){return B(_Fj(_Fk+_Fi|0));})]:[1,_Fk,_1l];};return B(_Fj(_Ff));});return [1,_Fe,_Fh];}else{return (_Fg<=_Fe)?[1,_Fe,_1l]:[0];}},_Fl=function(_Fm,_Fn,_Fo){if(_Fo>=_Fn){var _Fp=new T(function(){var _Fq=_Fn-_Fm|0,_Fr=function(_Fs){return (_Fs<=(_Fo-_Fq|0))?[1,_Fs,new T(function(){return B(_Fr(_Fs+_Fq|0));})]:[1,_Fs,_1l];};return B(_Fr(_Fn));});return [1,_Fm,_Fp];}else{return (_Fo>=_Fm)?[1,_Fm,_1l]:[0];}},_Ft=function(_Fu,_Fv){if(_Fv<_Fu){return new F(function(){return _Fd(_Fu,_Fv,-2147483648);});}else{return new F(function(){return _Fl(_Fu,_Fv,2147483647);});}},_Fw=function(_Fx,_Fy){return new F(function(){return _Ft(E(_Fx),E(_Fy));});},_Fz=function(_FA,_FB,_FC){if(_FB<_FA){return new F(function(){return _Fd(_FA,_FB,_FC);});}else{return new F(function(){return _Fl(_FA,_FB,_FC);});}},_FD=function(_FE,_FF,_FG){return new F(function(){return _Fz(E(_FE),E(_FF),E(_FG));});},_FH=function(_FI,_FJ){return new F(function(){return _F6(E(_FI),E(_FJ));});},_FK=function(_FL){return E(_FL);},_FM=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_FN=new T(function(){return B(err(_FM));}),_FO=function(_FP){var _FQ=E(_FP);return (_FQ==(-2147483648))?E(_FN):_FQ-1|0;},_FR=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_FS=new T(function(){return B(err(_FR));}),_FT=function(_FU){var _FV=E(_FU);return (_FV==2147483647)?E(_FS):_FV+1|0;},_FW=[0,_FT,_FO,_FK,_FK,_Fb,_Fw,_FH,_FD],_FX=function(_FY,_FZ){if(_FY<=0){if(_FY>=0){return new F(function(){return quot(_FY,_FZ);});}else{if(_FZ<=0){return new F(function(){return quot(_FY,_FZ);});}else{return quot(_FY+1|0,_FZ)-1|0;}}}else{if(_FZ>=0){if(_FY>=0){return new F(function(){return quot(_FY,_FZ);});}else{if(_FZ<=0){return new F(function(){return quot(_FY,_FZ);});}else{return quot(_FY+1|0,_FZ)-1|0;}}}else{return quot(_FY-1|0,_FZ)-1|0;}}},_G0=0,_G1=new T(function(){return B(_zC(_G0));}),_G2=new T(function(){return die(_G1);}),_G3=function(_G4,_G5){var _G6=E(_G5);switch(_G6){case -1:var _G7=E(_G4);if(_G7==(-2147483648)){return E(_G2);}else{return new F(function(){return _FX(_G7,-1);});}break;case 0:return E(_zF);default:return new F(function(){return _FX(_G4,_G6);});}},_G8=function(_G9,_Ga){return new F(function(){return _G3(E(_G9),E(_Ga));});},_Gb=0,_Gc=[0,_G2,_Gb],_Gd=function(_Ge,_Gf){var _Gg=E(_Ge),_Gh=E(_Gf);switch(_Gh){case -1:var _Gi=E(_Gg);if(_Gi==(-2147483648)){return E(_Gc);}else{if(_Gi<=0){if(_Gi>=0){var _Gj=quotRemI(_Gi,-1);return [0,_Gj[1],_Gj[2]];}else{var _Gk=quotRemI(_Gi,-1);return [0,_Gk[1],_Gk[2]];}}else{var _Gl=quotRemI(_Gi-1|0,-1);return [0,_Gl[1]-1|0,(_Gl[2]+(-1)|0)+1|0];}}break;case 0:return E(_zF);default:if(_Gg<=0){if(_Gg>=0){var _Gm=quotRemI(_Gg,_Gh);return [0,_Gm[1],_Gm[2]];}else{if(_Gh<=0){var _Gn=quotRemI(_Gg,_Gh);return [0,_Gn[1],_Gn[2]];}else{var _Go=quotRemI(_Gg+1|0,_Gh);return [0,_Go[1]-1|0,(_Go[2]+_Gh|0)-1|0];}}}else{if(_Gh>=0){if(_Gg>=0){var _Gp=quotRemI(_Gg,_Gh);return [0,_Gp[1],_Gp[2]];}else{if(_Gh<=0){var _Gq=quotRemI(_Gg,_Gh);return [0,_Gq[1],_Gq[2]];}else{var _Gr=quotRemI(_Gg+1|0,_Gh);return [0,_Gr[1]-1|0,(_Gr[2]+_Gh|0)-1|0];}}}else{var _Gs=quotRemI(_Gg-1|0,_Gh);return [0,_Gs[1]-1|0,(_Gs[2]+_Gh|0)+1|0];}}}},_Gt=function(_Gu,_Gv){var _Gw=_Gu%_Gv;if(_Gu<=0){if(_Gu>=0){return E(_Gw);}else{if(_Gv<=0){return E(_Gw);}else{var _Gx=E(_Gw);return (_Gx==0)?0:_Gx+_Gv|0;}}}else{if(_Gv>=0){if(_Gu>=0){return E(_Gw);}else{if(_Gv<=0){return E(_Gw);}else{var _Gy=E(_Gw);return (_Gy==0)?0:_Gy+_Gv|0;}}}else{var _Gz=E(_Gw);return (_Gz==0)?0:_Gz+_Gv|0;}}},_GA=function(_GB,_GC){var _GD=E(_GC);switch(_GD){case -1:return E(_Gb);case 0:return E(_zF);default:return new F(function(){return _Gt(E(_GB),_GD);});}},_GE=function(_GF,_GG){var _GH=E(_GF),_GI=E(_GG);switch(_GI){case -1:var _GJ=E(_GH);if(_GJ==(-2147483648)){return E(_G2);}else{return new F(function(){return quot(_GJ,-1);});}break;case 0:return E(_zF);default:return new F(function(){return quot(_GH,_GI);});}},_GK=function(_GL,_GM){var _GN=E(_GL),_GO=E(_GM);switch(_GO){case -1:var _GP=E(_GN);if(_GP==(-2147483648)){return E(_Gc);}else{var _GQ=quotRemI(_GP,-1);return [0,_GQ[1],_GQ[2]];}break;case 0:return E(_zF);default:var _GR=quotRemI(_GN,_GO);return [0,_GR[1],_GR[2]];}},_GS=function(_GT,_GU){var _GV=E(_GU);switch(_GV){case -1:return E(_Gb);case 0:return E(_zF);default:return E(_GT)%_GV;}},_GW=function(_GX){return new F(function(){return _bg(E(_GX));});},_GY=function(_GZ){return [0,E(B(_bg(E(_GZ)))),E(_F5)];},_H0=function(_H1,_H2){return imul(E(_H1),E(_H2))|0;},_H3=function(_H4,_H5){return E(_H4)+E(_H5)|0;},_H6=function(_H7,_H8){return E(_H7)-E(_H8)|0;},_H9=function(_Ha){var _Hb=E(_Ha);return (_Hb<0)? -_Hb:E(_Hb);},_Hc=function(_Hd){return new F(function(){return _cK(_Hd);});},_He=function(_Hf){return  -E(_Hf);},_Hg=-1,_Hh=0,_Hi=1,_Hj=function(_Hk){var _Hl=E(_Hk);return (_Hl>=0)?(E(_Hl)==0)?E(_Hh):E(_Hi):E(_Hg);},_Hm=[0,_H3,_H6,_H0,_He,_H9,_Hj,_Hc],_Hn=function(_Ho,_Hp){return E(_Ho)==E(_Hp);},_Hq=function(_Hr,_Hs){return E(_Hr)!=E(_Hs);},_Ht=[0,_Hn,_Hq],_Hu=function(_Hv,_Hw){var _Hx=E(_Hv),_Hy=E(_Hw);return (_Hx>_Hy)?E(_Hx):E(_Hy);},_Hz=function(_HA,_HB){var _HC=E(_HA),_HD=E(_HB);return (_HC>_HD)?E(_HD):E(_HC);},_HE=function(_HF,_HG){return (_HF>=_HG)?(_HF!=_HG)?2:1:0;},_HH=function(_HI,_HJ){return new F(function(){return _HE(E(_HI),E(_HJ));});},_HK=function(_HL,_HM){return E(_HL)>=E(_HM);},_HN=function(_HO,_HP){return E(_HO)>E(_HP);},_HQ=function(_HR,_HS){return E(_HR)<=E(_HS);},_HT=function(_HU,_HV){return E(_HU)<E(_HV);},_HW=[0,_Ht,_HH,_HT,_HQ,_HN,_HK,_Hu,_Hz],_HX=[0,_Hm,_HW,_GY],_HY=[0,_HX,_FW,_GE,_GS,_G8,_GA,_GK,_Gd,_GW],_HZ=function(_I0,_I1,_I2){while(1){if(!(_I1%2)){var _I3=B(_bm(_I0,_I0)),_I4=quot(_I1,2);_I0=_I3;_I1=_I4;continue;}else{var _I5=E(_I1);if(_I5==1){return new F(function(){return _bm(_I0,_I2);});}else{var _I3=B(_bm(_I0,_I0)),_I6=B(_bm(_I0,_I2));_I0=_I3;_I1=quot(_I5-1|0,2);_I2=_I6;continue;}}}},_I7=function(_I8,_I9){while(1){if(!(_I9%2)){var _Ia=B(_bm(_I8,_I8)),_Ib=quot(_I9,2);_I8=_Ia;_I9=_Ib;continue;}else{var _Ic=E(_I9);if(_Ic==1){return E(_I8);}else{return new F(function(){return _HZ(B(_bm(_I8,_I8)),quot(_Ic-1|0,2),_I8);});}}}},_Id=function(_Ie){return E(E(_Ie)[3]);},_If=function(_Ig){return E(E(_Ig)[1]);},_Ih=function(_Ii){return E(E(_Ii)[2]);},_Ij=function(_Ik){return E(E(_Ik)[2]);},_Il=function(_Im){return E(E(_Im)[3]);},_In=[0,0],_Io=[0,2],_Ip=function(_Iq){return E(E(_Iq)[7]);},_Ir=function(_Is){return E(E(_Is)[4]);},_It=function(_Iu,_Iv){var _Iw=B(_F1(_Iu)),_Ix=new T(function(){return B(_F3(_Iw));}),_Iy=new T(function(){return B(A(_Ir,[_Iu,_Iv,new T(function(){return B(A(_Ip,[_Ix,_Io]));})]));});return new F(function(){return A(_T,[B(_If(B(_Ih(_Iw)))),_Iy,new T(function(){return B(A(_Ip,[_Ix,_In]));})]);});},_Iz=new T(function(){return B(unCStr("Negative exponent"));}),_IA=new T(function(){return B(err(_Iz));}),_IB=function(_IC){return E(E(_IC)[3]);},_ID=function(_IE,_IF,_IG,_IH){var _II=B(_F1(_IF)),_IJ=new T(function(){return B(_F3(_II));}),_IK=B(_Ih(_II));if(!B(A(_Il,[_IK,_IH,new T(function(){return B(A(_Ip,[_IJ,_In]));})]))){if(!B(A(_T,[B(_If(_IK)),_IH,new T(function(){return B(A(_Ip,[_IJ,_In]));})]))){var _IL=new T(function(){return B(A(_Ip,[_IJ,_Io]));}),_IM=new T(function(){return B(A(_Ip,[_IJ,_F5]));}),_IN=B(_If(_IK)),_IO=function(_IP,_IQ,_IR){while(1){var _IS=B((function(_IT,_IU,_IV){if(!B(_It(_IF,_IU))){if(!B(A(_T,[_IN,_IU,_IM]))){var _IW=new T(function(){return B(A(_IB,[_IF,new T(function(){return B(A(_Ij,[_IJ,_IU,_IM]));}),_IL]));});_IP=new T(function(){return B(A(_Id,[_IE,_IT,_IT]));});_IQ=_IW;_IR=new T(function(){return B(A(_Id,[_IE,_IT,_IV]));});return null;}else{return new F(function(){return A(_Id,[_IE,_IT,_IV]);});}}else{var _IX=_IV;_IP=new T(function(){return B(A(_Id,[_IE,_IT,_IT]));});_IQ=new T(function(){return B(A(_IB,[_IF,_IU,_IL]));});_IR=_IX;return null;}})(_IP,_IQ,_IR));if(_IS!=null){return _IS;}}},_IY=_IG,_IZ=_IH;while(1){var _J0=B((function(_J1,_J2){if(!B(_It(_IF,_J2))){if(!B(A(_T,[_IN,_J2,_IM]))){var _J3=new T(function(){return B(A(_IB,[_IF,new T(function(){return B(A(_Ij,[_IJ,_J2,_IM]));}),_IL]));});return new F(function(){return _IO(new T(function(){return B(A(_Id,[_IE,_J1,_J1]));}),_J3,_J1);});}else{return E(_J1);}}else{_IY=new T(function(){return B(A(_Id,[_IE,_J1,_J1]));});_IZ=new T(function(){return B(A(_IB,[_IF,_J2,_IL]));});return null;}})(_IY,_IZ));if(_J0!=null){return _J0;}}}else{return new F(function(){return A(_Ip,[_IE,_F5]);});}}else{return E(_IA);}},_J4=new T(function(){return B(err(_Iz));}),_J5=function(_J6,_J7){var _J8=B(_rV(_J7)),_J9=_J8[1],_Ja=_J8[2],_Jb=new T(function(){return B(_F3(new T(function(){return B(_F1(_J6));})));});if(_Ja<0){var _Jc= -_Ja;if(_Jc>=0){var _Jd=E(_Jc);if(!_Jd){var _Je=E(_F5);}else{var _Je=B(_I7(_Df,_Jd));}if(!B(_zK(_Je,_A1))){var _Jf=B(_zS(_J9,_Je));return [0,new T(function(){return B(A(_Ip,[_Jb,_Jf[1]]));}),new T(function(){return B(_zG(_Jf[2],_Ja));})];}else{return E(_zF);}}else{return E(_J4);}}else{var _Jg=new T(function(){var _Jh=new T(function(){return B(_ID(_Jb,_HY,new T(function(){return B(A(_Ip,[_Jb,_Df]));}),_Ja));});return B(A(_Id,[_Jb,new T(function(){return B(A(_Ip,[_Jb,_J9]));}),_Jh]));});return [0,_Jg,_Bz];}},_Ji=function(_Jj){return E(E(_Jj)[1]);},_Jk=function(_Jl,_Jm){var _Jn=B(_J5(_Jl,E(_Jm))),_Jo=_Jn[1];if(E(_Jn[2])<=0){return E(_Jo);}else{var _Jp=B(_F3(B(_F1(_Jl))));return new F(function(){return A(_Ji,[_Jp,_Jo,new T(function(){return B(A(_Ip,[_Jp,_yU]));})]);});}},_Jq=function(_Jr,_Js){var _Jt=B(_J5(_Jr,E(_Js))),_Ju=_Jt[1];if(E(_Jt[2])>=0){return E(_Ju);}else{var _Jv=B(_F3(B(_F1(_Jr))));return new F(function(){return A(_Ij,[_Jv,_Ju,new T(function(){return B(A(_Ip,[_Jv,_yU]));})]);});}},_Jw=function(_Jx,_Jy){var _Jz=B(_J5(_Jx,E(_Jy)));return [0,_Jz[1],_Jz[2]];},_JA=function(_JB,_JC){var _JD=B(_J5(_JB,_JC)),_JE=_JD[1],_JF=E(_JD[2]),_JG=new T(function(){var _JH=B(_F3(B(_F1(_JB))));if(_JF>=0){return B(A(_Ji,[_JH,_JE,new T(function(){return B(A(_Ip,[_JH,_yU]));})]));}else{return B(A(_Ij,[_JH,_JE,new T(function(){return B(A(_Ip,[_JH,_yU]));})]));}}),_JI=function(_JJ){var _JK=_JJ-0.5;return (_JK>=0)?(E(_JK)==0)?(!B(_It(_JB,_JE)))?E(_JG):E(_JE):E(_JG):E(_JE);},_JL=E(_JF);if(!_JL){return new F(function(){return _JI(0);});}else{if(_JL<=0){var _JM= -_JL-0.5;return (_JM>=0)?(E(_JM)==0)?(!B(_It(_JB,_JE)))?E(_JG):E(_JE):E(_JG):E(_JE);}else{return new F(function(){return _JI(_JL);});}}},_JN=function(_JO,_JP){return new F(function(){return _JA(_JO,E(_JP));});},_JQ=function(_JR,_JS){return E(B(_J5(_JR,E(_JS)))[1]);},_JT=[0,_F0,_C8,_Jw,_JQ,_JN,_Jk,_Jq],_JU=[0,_JT,_CA,_Dg,_Dd,_Dl,_D1,_D4,_Da,_DN,_DK,_Dv,_Ds,_Dn,_Dy,_Dq,_CY],_JV=0,_JW=1,_JX=2,_JY=1,_JZ=function(_K0){return new F(function(){return err(B(unAppCStr("Char.intToDigit: not a digit ",new T(function(){if(_K0>=0){var _K1=jsShowI(_K0);return fromJSStr(_K1);}else{var _K2=jsShowI(_K0);return fromJSStr(_K2);}}))));});},_K3=function(_K4){var _K5=function(_K6){if(_K4<10){return new F(function(){return _JZ(_K4);});}else{if(_K4>15){return new F(function(){return _JZ(_K4);});}else{return (97+_K4|0)-10|0;}}};if(_K4<0){return new F(function(){return _K5(_);});}else{if(_K4>9){return new F(function(){return _K5(_);});}else{return 48+_K4|0;}}},_K7=function(_K8){return new F(function(){return _K3(E(_K8));});},_K9=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_Ka=function(_Kb){return new F(function(){return _7q([0,new T(function(){return B(_7E(_Kb,_K9));})],_78);});},_Kc=new T(function(){return B(_Ka("GHC\\Float.hs:622:11-64|d : ds\'"));}),_Kd=0,_Ke=function(_Kf,_Kg){if(E(_Kf)<=0){var _Kh=B(_bc(_K7,[1,_Kd,_Kg]));return (_Kh[0]==0)?E(_Kc):[0,_Kh[1],_Kh[2]];}else{var _Ki=B(_bc(_K7,_Kg));return (_Ki[0]==0)?E(_Kc):[0,_Ki[1],_Ki[2]];}},_Kj=function(_Kk){return E(E(_Kk)[1]);},_Kl=function(_Km){return E(E(_Km)[1]);},_Kn=function(_Ko){return E(E(_Ko)[1]);},_Kp=function(_Kq){return E(E(_Kq)[1]);},_Kr=function(_Ks){return E(E(_Ks)[2]);},_Kt=46,_Ku=48,_Kv=new T(function(){return B(unCStr("0"));}),_Kw=function(_Kx,_Ky,_Kz){while(1){var _KA=B((function(_KB,_KC,_KD){var _KE=E(_KB);if(!_KE){var _KF=B(_sU(_KC,_1l));if(!_KF[0]){return new F(function(){return _16(_Kv,[1,_Kt,new T(function(){var _KG=E(_KD);if(!_KG[0]){return E(_Kv);}else{return E(_KG);}})]);});}else{return new F(function(){return _16(_KF,[1,_Kt,new T(function(){var _KH=E(_KD);if(!_KH[0]){return E(_Kv);}else{return E(_KH);}})]);});}}else{var _KI=E(_KD);if(!_KI[0]){var _KJ=[1,_Ku,_KC];_Kx=_KE-1|0;_Ky=_KJ;_Kz=_1l;return null;}else{var _KJ=[1,_KI[1],_KC];_Kx=_KE-1|0;_Ky=_KJ;_Kz=_KI[2];return null;}}})(_Kx,_Ky,_Kz));if(_KA!=null){return _KA;}}},_KK=function(_KL){return new F(function(){return _1g(0,E(_KL),_1l);});},_KM=function(_KN,_KO,_KP){return new F(function(){return _1g(E(_KN),E(_KO),_KP);});},_KQ=function(_KR,_KS){return new F(function(){return _1g(0,E(_KR),_KS);});},_KT=function(_KU,_KV){return new F(function(){return _6r(_KQ,_KU,_KV);});},_KW=[0,_KM,_KK,_KT],_KX=0,_KY=function(_KZ,_L0,_L1){return new F(function(){return A(_KZ,[[1,_6o,new T(function(){return B(A(_L0,[_L1]));})]]);});},_L2=new T(function(){return B(unCStr(": empty list"));}),_L3=function(_L4){return new F(function(){return err(B(_16(_wS,new T(function(){return B(_16(_L4,_L2));},1))));});},_L5=new T(function(){return B(unCStr("foldr1"));}),_L6=new T(function(){return B(_L3(_L5));}),_L7=function(_L8,_L9){var _La=E(_L9);if(!_La[0]){return E(_L6);}else{var _Lb=_La[1],_Lc=E(_La[2]);if(!_Lc[0]){return E(_Lb);}else{return new F(function(){return A(_L8,[_Lb,new T(function(){return B(_L7(_L8,_Lc));})]);});}}},_Ld=new T(function(){return B(unCStr(" out of range "));}),_Le=new T(function(){return B(unCStr("}.index: Index "));}),_Lf=new T(function(){return B(unCStr("Ix{"));}),_Lg=[1,_1e,_1l],_Lh=[1,_1e,_Lg],_Li=0,_Lj=function(_Lk){return E(E(_Lk)[1]);},_Ll=function(_Lm,_Ln,_Lo,_Lp,_Lq){var _Lr=new T(function(){var _Ls=new T(function(){var _Lt=new T(function(){var _Lu=new T(function(){var _Lv=new T(function(){return B(A(_L7,[_KY,[1,new T(function(){return B(A(_Lj,[_Lo,_Li,_Lp]));}),[1,new T(function(){return B(A(_Lj,[_Lo,_Li,_Lq]));}),_1l]],_Lh]));});return B(_16(_Ld,[1,_1f,[1,_1f,_Lv]]));});return B(A(_Lj,[_Lo,_KX,_Ln,[1,_1e,_Lu]]));});return B(_16(_Le,[1,_1f,_Lt]));},1);return B(_16(_Lm,_Ls));},1);return new F(function(){return err(B(_16(_Lf,_Lr)));});},_Lw=function(_Lx,_Ly,_Lz,_LA,_LB){return new F(function(){return _Ll(_Lx,_Ly,_LB,_Lz,_LA);});},_LC=function(_LD,_LE,_LF,_LG){var _LH=E(_LF);return new F(function(){return _Lw(_LD,_LE,_LH[1],_LH[2],_LG);});},_LI=function(_LJ,_LK,_LL,_LM){return new F(function(){return _LC(_LM,_LL,_LK,_LJ);});},_LN=new T(function(){return B(unCStr("Int"));}),_LO=function(_LP,_LQ,_LR){return new F(function(){return _LI(_KW,[0,_LQ,_LR],_LP,_LN);});},_LS=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_LT=new T(function(){return B(err(_LS));}),_LU=1100,_LV=[0,_Kd,_LU],_LW=function(_LX){return new F(function(){return _LI(_KW,_LV,_LX,_LN);});},_LY=function(_){var _LZ=newArr(1101,_LT),_M0=_LZ,_M1=0;while(1){var _M2=B((function(_M3,_){if(0>_M3){return new F(function(){return _LW(_M3);});}else{if(_M3>1100){return new F(function(){return _LW(_M3);});}else{var _=_M0[_M3]=new T(function(){if(_M3>=0){var _M4=E(_M3);if(!_M4){return E(_F5);}else{return B(_I7(_Df,_M4));}}else{return E(_J4);}}),_M5=E(_M3);if(_M5==1100){return [0,E(_Kd),E(_LU),1101,_M0];}else{_M1=_M5+1|0;return null;}}}})(_M1,_));if(_M2!=null){return _M2;}}},_M6=function(_M7){var _M8=B(A(_M7,[_]));return E(_M8);},_M9=new T(function(){return B(_M6(_LY));}),_Ma=[0,10],_Mb=324,_Mc=[0,_Kd,_Mb],_Md=function(_Me){return new F(function(){return _LI(_KW,_Mc,_Me,_LN);});},_Mf=function(_){var _Mg=newArr(325,_LT),_Mh=_Mg,_Mi=0;while(1){var _Mj=B((function(_Mk,_){if(0>_Mk){return new F(function(){return _Md(_Mk);});}else{if(_Mk>324){return new F(function(){return _Md(_Mk);});}else{var _=_Mh[_Mk]=new T(function(){if(_Mk>=0){var _Ml=E(_Mk);if(!_Ml){return E(_F5);}else{return B(_I7(_Ma,_Ml));}}else{return E(_J4);}}),_Mm=E(_Mk);if(_Mm==324){return [0,E(_Kd),E(_Mb),325,_Mh];}else{_Mi=_Mm+1|0;return null;}}}})(_Mi,_));if(_Mj!=null){return _Mj;}}},_Mn=new T(function(){return B(_M6(_Mf));}),_Mo=function(_Mp,_Mq){var _Mr=function(_Ms){if(!B(_zK(_Mp,_Ma))){if(_Mq>=0){var _Mt=E(_Mq);if(!_Mt){return E(_F5);}else{return new F(function(){return _I7(_Mp,_Mt);});}}else{return E(_J4);}}else{if(_Mq>324){if(_Mq>=0){var _Mu=E(_Mq);if(!_Mu){return E(_F5);}else{return new F(function(){return _I7(_Mp,_Mu);});}}else{return E(_J4);}}else{var _Mv=E(_Mn),_Mw=E(_Mv[1]),_Mx=E(_Mv[2]);if(_Mw>_Mq){return new F(function(){return _LO(_Mq,_Mw,_Mx);});}else{if(_Mq>_Mx){return new F(function(){return _LO(_Mq,_Mw,_Mx);});}else{return E(_Mv[4][_Mq-_Mw|0]);}}}}};if(!B(_zK(_Mp,_Df))){return new F(function(){return _Mr(_);});}else{if(_Mq<0){return new F(function(){return _Mr(_);});}else{if(_Mq>1100){return new F(function(){return _Mr(_);});}else{var _My=E(_M9),_Mz=E(_My[1]),_MA=E(_My[2]);if(_Mz>_Mq){return new F(function(){return _LO(_Mq,_Mz,_MA);});}else{if(_Mq>_MA){return new F(function(){return _LO(_Mq,_Mz,_MA);});}else{return E(_My[4][_Mq-_Mz|0]);}}}}}},_MB=function(_MC){return E(E(_MC)[6]);},_MD=function(_ME){return E(E(_ME)[4]);},_MF=function(_MG){var _MH=E(_MG);if(!_MH[0]){return _MH[1];}else{return new F(function(){return I_toNumber(_MH[1]);});}},_MI=function(_MJ){return E(E(_MJ)[3]);},_MK=function(_ML){return E(E(_ML)[5]);},_MM=[1,_Kd,_1l],_MN=function(_MO,_MP){while(1){var _MQ=E(_MO);if(!_MQ[0]){var _MR=E(_MQ[1]);if(_MR==(-2147483648)){_MO=[1,I_fromInt(-2147483648)];continue;}else{var _MS=E(_MP);if(!_MS[0]){return [0,quot(_MR,_MS[1])];}else{_MO=[1,I_fromInt(_MR)];_MP=_MS;continue;}}}else{var _MT=_MQ[1],_MU=E(_MP);return (_MU[0]==0)?[0,I_toInt(I_quot(_MT,I_fromInt(_MU[1])))]:[1,I_quot(_MT,_MU[1])];}}},_MV=function(_MW,_MX,_MY){if(!B(A(_T,[B(_If(B(_Ih(B(_Kp(B(_Kn(_MW)))))))),_MY,new T(function(){return B(A(_Ip,[B(_Kl(B(_Kj(B(_Kr(_MW)))))),_A1]));})]))){var _MZ=new T(function(){return B(A(_MI,[_MW,_MY]));}),_N0=new T(function(){return B(A(_MD,[_MW,_MY]));}),_N1=new T(function(){return E(B(A(_MK,[_MW,_MY]))[1])-E(_N0)|0;}),_N2=new T(function(){return B(A(_MB,[_MW,_MY]));}),_N3=new T(function(){return E(E(_N2)[2]);}),_N4=new T(function(){var _N5=E(_N3),_N6=E(_N1)-_N5|0;if(_N6<=0){return [0,new T(function(){return E(E(_N2)[1]);}),_N5];}else{return [0,new T(function(){var _N7=B(_Mo(_MZ,_N6));if(!B(_zK(_N7,_A1))){return B(_MN(E(_N2)[1],_N7));}else{return E(_zF);}}),_N5+_N6|0];}}),_N8=new T(function(){return E(E(_N4)[2]);}),_N9=new T(function(){return E(E(_N4)[1]);}),_Na=new T(function(){var _Nb=E(_N8);if(_Nb<0){if(_Nb<=E(_N1)){return [0,new T(function(){return B(_bm(_N9,_Df));}),new T(function(){return B(_bm(B(_Mo(_MZ, -_Nb)),_Df));}),_yU,_yU];}else{if(!B(_zK(_N9,B(_Mo(_MZ,E(_N0)-1|0))))){return [0,new T(function(){return B(_bm(_N9,_Df));}),new T(function(){return B(_bm(B(_Mo(_MZ, -_Nb)),_Df));}),_yU,_yU];}else{return [0,new T(function(){return B(_bm(B(_bm(_N9,_MZ)),_Df));}),new T(function(){return B(_bm(B(_Mo(_MZ, -_Nb+1|0)),_Df));}),_MZ,_yU];}}}else{var _Nc=new T(function(){return B(_Mo(_MZ,_Nb));});if(!B(_zK(_N9,B(_Mo(_MZ,E(_N0)-1|0))))){return [0,new T(function(){return B(_bm(B(_bm(_N9,_Nc)),_Df));}),_Df,_Nc,_Nc];}else{return [0,new T(function(){return B(_bm(B(_bm(B(_bm(_N9,_Nc)),_MZ)),_Df));}),new T(function(){return B(_bm(_Df,_MZ));}),new T(function(){return B(_bm(_Nc,_MZ));}),_Nc];}}}),_Nd=new T(function(){return E(E(_Na)[2]);}),_Ne=new T(function(){return E(E(_Na)[3]);}),_Nf=new T(function(){return E(E(_Na)[1]);}),_Ng=new T(function(){var _Nh=new T(function(){return B(_aS(_Nf,_Ne));}),_Ni=function(_Nj){var _Nk=(Math.log(B(_MF(B(_aS(_N9,_yU)))))+E(_N8)*Math.log(B(_MF(_MZ))))/Math.log(B(_MF(_MX))),_Nl=_Nk&4294967295;return (_Nl>=_Nk)?E(_Nl):_Nl+1|0;},_Nm=function(_Nn){while(1){if(_Nn<0){if(!B(_cN(B(_bm(B(_Mo(_MX, -_Nn)),_Nh)),_Nd))){var _No=_Nn+1|0;_Nn=_No;continue;}else{return E(_Nn);}}else{if(!B(_cN(_Nh,B(_bm(B(_Mo(_MX,_Nn)),_Nd))))){var _No=_Nn+1|0;_Nn=_No;continue;}else{return E(_Nn);}}}};if(!B(_zK(_MZ,_Df))){return B(_Nm(B(_Ni(_))));}else{if(!B(_zK(_MX,_Ma))){return B(_Nm(B(_Ni(_))));}else{var _Np=(E(_N0)-1|0)+E(_N3)|0;if(_Np<0){return B(_Nm(quot(imul(_Np,8651)|0,28738)));}else{return B(_Nm(quot(imul(_Np,8651)|0,28738)+1|0));}}}}),_Nq=new T(function(){var _Nr=E(_Ng),_Ns=function(_Nt,_Nu,_Nv,_Nw,_Nx){while(1){var _Ny=B((function(_Nz,_NA,_NB,_NC,_ND){if(!B(_zK(_NB,_A1))){var _NE=B(_zS(B(_bm(_NA,_MX)),_NB)),_NF=_NE[1],_NG=_NE[2],_NH=B(_bm(_ND,_MX)),_NI=B(_bm(_NC,_MX));if(!B(_wk(_NG,_NH))){if(!B(_A8(B(_aS(_NG,_NI)),_NB))){var _NJ=[1,_NF,_Nz],_NK=_NB;_Nt=_NJ;_Nu=_NG;_Nv=_NK;_Nw=_NI;_Nx=_NH;return null;}else{return [1,new T(function(){return B(_aS(_NF,_yU));}),_Nz];}}else{return (!B(_A8(B(_aS(_NG,_NI)),_NB)))?[1,_NF,_Nz]:(!B(_wk(B(_bm(_NG,_Df)),_NB)))?[1,new T(function(){return B(_aS(_NF,_yU));}),_Nz]:[1,_NF,_Nz];}}else{return E(_zF);}})(_Nt,_Nu,_Nv,_Nw,_Nx));if(_Ny!=null){return _Ny;}}};if(_Nr<0){var _NL=B(_Mo(_MX, -_Nr));return B(_bc(_Hc,B(_sU(B(_Ns(_1l,B(_bm(_Nf,_NL)),_Nd,B(_bm(_Ne,_NL)),B(_bm(E(_Na)[4],_NL)))),_1l))));}else{return B(_bc(_Hc,B(_sU(B(_Ns(_1l,_Nf,B(_bm(_Nd,B(_Mo(_MX,_Nr)))),_Ne,E(_Na)[4])),_1l))));}});return [0,_Nq,_Ng];}else{return [0,_MM,_Kd];}},_NM=function(_NN){var _NO=E(_NN);return (_NO==1)?E(_MM):[1,_Kd,new T(function(){return B(_NM(_NO-1|0));})];},_NP=function(_NQ,_NR){while(1){var _NS=E(_NR);if(!_NS[0]){return true;}else{if(!B(A(_NQ,[_NS[1]]))){return false;}else{_NR=_NS[2];continue;}}}},_NT=function(_NU){return (E(_NU)%2==0)?true:false;},_NV=new T(function(){return B(unCStr("roundTo: bad Value"));}),_NW=new T(function(){return B(err(_NV));}),_NX=function(_NY){return (E(_NY)==0)?true:false;},_NZ=function(_O0,_O1,_O2){var _O3=new T(function(){return quot(E(_O0),2);}),_O4=function(_O5,_O6,_O7){var _O8=E(_O7);if(!_O8[0]){return [0,_Kd,new T(function(){var _O9=E(_O5);if(0>=_O9){return [0];}else{return B(_NM(_O9));}})];}else{var _Oa=_O8[1],_Ob=_O8[2],_Oc=E(_O5);if(!_Oc){var _Od=E(_Oa),_Oe=E(_O3);return (_Od!=_Oe)?[0,new T(function(){if(_Od<_Oe){return E(_Kd);}else{return E(_JY);}}),_1l]:(!E(_O6))?[0,new T(function(){if(_Od<_Oe){return E(_Kd);}else{return E(_JY);}}),_1l]:(!B(_NP(_NX,_Ob)))?[0,new T(function(){if(_Od<_Oe){return E(_Kd);}else{return E(_JY);}}),_1l]:[0,_Kd,_1l];}else{var _Of=B(_O4(_Oc-1|0,new T(function(){return B(_NT(_Oa));},1),_Ob)),_Og=_Of[2],_Oh=E(_Of[1])+E(_Oa)|0;return (_Oh!=E(_O0))?[0,_Kd,[1,_Oh,_Og]]:[0,_JY,[1,_Kd,_Og]];}}},_Oi=B(_O4(_O1,_cy,_O2)),_Oj=_Oi[1],_Ok=_Oi[2];switch(E(_Oj)){case 0:return [0,_Oj,_Ok];case 1:return [0,_JY,[1,_JY,_Ok]];default:return E(_NW);}},_Ol=function(_Om,_On){var _Oo=E(_On);if(!_Oo[0]){return [0,_1l,_1l];}else{var _Op=_Oo[1],_Oq=_Oo[2],_Or=E(_Om);if(_Or==1){return [0,[1,_Op,_1l],_Oq];}else{var _Os=new T(function(){var _Ot=B(_Ol(_Or-1|0,_Oq));return [0,_Ot[1],_Ot[2]];});return [0,[1,_Op,new T(function(){return E(E(_Os)[1]);})],new T(function(){return E(E(_Os)[2]);})];}}},_Ou=new T(function(){return B(unCStr("e0"));}),_Ov=[1,_Ku,_Ou],_Ow=function(_Ox){var _Oy=E(_Ox);return (_Oy==1)?E(_Ov):[1,_Ku,new T(function(){return B(_Ow(_Oy-1|0));})];},_Oz=10,_OA=function(_OB,_OC){var _OD=E(_OC);return (_OD[0]==0)?[0]:[1,_OB,new T(function(){return B(_OA(_OD[1],_OD[2]));})];},_OE=new T(function(){return B(unCStr("init"));}),_OF=new T(function(){return B(_L3(_OE));}),_OG=function(_OH){return E(E(_OH)[12]);},_OI=function(_OJ){return E(E(_OJ)[11]);},_OK=function(_OL){return E(E(_OL)[14]);},_OM=new T(function(){return B(unCStr("NaN"));}),_ON=new T(function(){return B(unCStr("-Infinity"));}),_OO=new T(function(){return B(unCStr("formatRealFloat/doFmt/FFExponent: []"));}),_OP=new T(function(){return B(err(_OO));}),_OQ=new T(function(){return B(unCStr("Infinity"));}),_OR=[1,_Kt,_1l],_OS=101,_OT=new T(function(){return B(_Ka("GHC\\Float.hs:594:12-70|(d : ds\')"));}),_OU=new T(function(){return B(unCStr("0.0e0"));}),_OV=function(_OW){return E(E(_OW)[4]);},_OX=45,_OY=function(_OZ,_P0,_P1,_P2,_P3){if(!B(A(_OI,[_OZ,_P3]))){var _P4=new T(function(){return B(_Kl(new T(function(){return B(_Kj(new T(function(){return B(_Kr(_OZ));})));})));});if(!B(A(_OG,[_OZ,_P3]))){var _P5=function(_P6,_P7,_P8){while(1){var _P9=B((function(_Pa,_Pb,_Pc){switch(E(_Pa)){case 0:var _Pd=E(_P1);if(!_Pd[0]){var _Pe=B(_bc(_K7,_Pb));if(!_Pe[0]){return E(_OP);}else{var _Pf=_Pe[2],_Pg=E(_Pe[1]),_Ph=function(_Pi){var _Pj=E(_Pf);if(!_Pj[0]){var _Pk=new T(function(){return B(unAppCStr(".0e",new T(function(){return B(_1g(0,E(_Pc)-1|0,_1l));})));});return [1,_Pg,_Pk];}else{var _Pl=new T(function(){var _Pm=new T(function(){return B(unAppCStr("e",new T(function(){return B(_1g(0,E(_Pc)-1|0,_1l));})));},1);return B(_16(_Pj,_Pm));});return [1,_Pg,[1,_Kt,_Pl]];}};if(E(_Pg)==48){if(!E(_Pf)[0]){return E(_OU);}else{return new F(function(){return _Ph(_);});}}else{return new F(function(){return _Ph(_);});}}}else{var _Pn=new T(function(){var _Po=E(_Pd[1]);if(_Po>1){return E(_Po);}else{return E(_JY);}}),_Pp=function(_Pq){var _Pr=new T(function(){var _Ps=B(_NZ(_Oz,new T(function(){return E(_Pn)+1|0;},1),_Pb));return [0,_Ps[1],_Ps[2]];}),_Pt=new T(function(){return E(E(_Pr)[1]);}),_Pu=new T(function(){if(E(_Pt)<=0){var _Pv=B(_bc(_K7,E(_Pr)[2]));if(!_Pv[0]){return E(_OT);}else{return [0,_Pv[1],_Pv[2]];}}else{var _Pw=E(E(_Pr)[2]);if(!_Pw[0]){return E(_OF);}else{var _Px=B(_bc(_K7,B(_OA(_Pw[1],_Pw[2]))));if(!_Px[0]){return E(_OT);}else{return [0,_Px[1],_Px[2]];}}}}),_Py=new T(function(){return B(_16(E(_Pu)[2],[1,_OS,new T(function(){return B(_1g(0,(E(_Pc)-1|0)+E(_Pt)|0,_1l));})]));});return [1,new T(function(){return E(E(_Pu)[1]);}),[1,_Kt,_Py]];},_Pz=E(_Pb);if(!_Pz[0]){return new F(function(){return _Pp(_);});}else{if(!E(_Pz[1])){if(!E(_Pz[2])[0]){return [1,_Ku,[1,_Kt,new T(function(){var _PA=E(_Pn);if(0>=_PA){return E(_Ou);}else{return B(_Ow(_PA));}})]];}else{return new F(function(){return _Pp(_);});}}else{return new F(function(){return _Pp(_);});}}}break;case 1:var _PB=E(_P1);if(!_PB[0]){var _PC=E(_Pc);if(_PC>0){return new F(function(){return _Kw(_PC,_1l,new T(function(){return B(_bc(_K7,_Pb));},1));});}else{var _PD=new T(function(){var _PE= -_PC;if(0>=_PE){return B(_bc(_K7,_Pb));}else{var _PF=new T(function(){return B(_bc(_K7,_Pb));}),_PG=function(_PH){var _PI=E(_PH);return (_PI==1)?[1,_Ku,_PF]:[1,_Ku,new T(function(){return B(_PG(_PI-1|0));})];};return B(_PG(_PE));}});return new F(function(){return unAppCStr("0.",_PD);});}}else{var _PJ=_PB[1],_PK=E(_Pc);if(_PK<0){var _PL=new T(function(){var _PM= -_PK;if(0>=_PM){var _PN=B(_NZ(_Oz,new T(function(){var _PO=E(_PJ);if(_PO>0){return E(_PO);}else{return E(_Kd);}},1),_Pb));return B(_Ke(_PN[1],_PN[2]));}else{var _PP=function(_PQ){var _PR=E(_PQ);return (_PR==1)?[1,_Kd,_Pb]:[1,_Kd,new T(function(){return B(_PP(_PR-1|0));})];},_PS=B(_NZ(_Oz,new T(function(){var _PT=E(_PJ);if(_PT>0){return E(_PT);}else{return E(_Kd);}},1),B(_PP(_PM))));return B(_Ke(_PS[1],_PS[2]));}});return [1,new T(function(){return E(E(_PL)[1]);}),new T(function(){var _PU=E(E(_PL)[2]);if(!_PU[0]){if(!E(_P2)){return [0];}else{return E(_OR);}}else{return [1,_Kt,_PU];}})];}else{var _PV=B(_NZ(_Oz,new T(function(){var _PW=E(_PJ);if(_PW>0){return _PW+_PK|0;}else{return E(_PK);}},1),_Pb)),_PX=_PV[2],_PY=_PK+E(_PV[1])|0;if(_PY>0){var _PZ=B(_Ol(_PY,B(_bc(_K7,_PX)))),_Q0=_PZ[2],_Q1=E(_PZ[1]);if(!_Q1[0]){return new F(function(){return _16(_Kv,new T(function(){var _Q2=E(_Q0);if(!_Q2[0]){if(!E(_P2)){return [0];}else{return E(_OR);}}else{return [1,_Kt,_Q2];}},1));});}else{return new F(function(){return _16(_Q1,new T(function(){var _Q3=E(_Q0);if(!_Q3[0]){if(!E(_P2)){return [0];}else{return E(_OR);}}else{return [1,_Kt,_Q3];}},1));});}}else{return new F(function(){return _16(_Kv,new T(function(){var _Q4=B(_bc(_K7,_PX));if(!_Q4[0]){if(!E(_P2)){return [0];}else{return E(_OR);}}else{return [1,_Kt,_Q4];}},1));});}}}break;default:var _Q5=E(_Pc);if(_Q5>=0){if(_Q5<=7){var _Q6=_Pb;_P6=_JW;_P7=_Q6;_P8=_Q5;return null;}else{var _Q6=_Pb;_P6=_JV;_P7=_Q6;_P8=_Q5;return null;}}else{var _Q6=_Pb;_P6=_JV;_P7=_Q6;_P8=_Q5;return null;}}})(_P6,_P7,_P8));if(_P9!=null){return _P9;}}},_Q7=function(_Q8){var _Q9=new T(function(){var _Qa=B(_MV(_OZ,_Ma,new T(function(){return B(A(_OV,[_P4,_P3]));})));return B(_P5(_P0,_Qa[1],_Qa[2]));});return [1,_OX,_Q9];};if(!B(A(_Il,[B(_Ih(B(_Kp(B(_Kn(_OZ)))))),_P3,new T(function(){return B(A(_Ip,[_P4,_A1]));})]))){if(!B(A(_OK,[_OZ,_P3]))){var _Qb=B(_MV(_OZ,_Ma,_P3));return new F(function(){return _P5(_P0,_Qb[1],_Qb[2]);});}else{return new F(function(){return _Q7(_);});}}else{return new F(function(){return _Q7(_);});}}else{return (!B(A(_Il,[B(_Ih(B(_Kp(B(_Kn(_OZ)))))),_P3,new T(function(){return B(A(_Ip,[_P4,_A1]));})])))?E(_OQ):E(_ON);}}else{return E(_OM);}},_Qc=function(_Qd){var _Qe=u_towupper(E(_Qd));if(_Qe>>>0>1114111){return new F(function(){return _cI(_Qe);});}else{return _Qe;}},_Qf=function(_Qg,_Qh,_Qi,_Qj){var _Qk=u_iswupper(_Qg),_Ql=_Qk,_Qm=u_towlower(_Qg);if(_Qm>>>0>1114111){var _Qn=B(_cI(_Qm));}else{switch(_Qm){case 101:var _Qo=B(_OY(_JU,_JV,_Qh,_cx,_Qj));break;case 102:if(!E(_Qi)){var _Qp=B(_OY(_JU,_JW,_Qh,_cx,_Qj));}else{var _Qp=B(_OY(_JU,_JW,_Qh,_cy,_Qj));}var _Qo=_Qp;break;case 103:if(!E(_Qi)){var _Qq=B(_OY(_JU,_JX,_Qh,_cx,_Qj));}else{var _Qq=B(_OY(_JU,_JX,_Qh,_cy,_Qj));}var _Qo=_Qq;break;default:var _Qo=E(_yG);}var _Qn=_Qo;}if(!E(_Ql)){var _Qr=E(_Qn);return (_Qr[0]==0)?[0,_1l,_1l]:(E(_Qr[1])==45)?[0,_yE,_Qr[2]]:[0,_1l,_Qr];}else{var _Qs=B(_bc(_Qc,_Qn));return (_Qs[0]==0)?[0,_1l,_1l]:(E(_Qs[1])==45)?[0,_yE,_Qs[2]]:[0,_1l,_Qs];}},_Qt=new T(function(){return B(unCStr(" "));}),_Qu=new T(function(){return B(unCStr("+"));}),_Qv=48,_Qw=32,_Qx=function(_Qy,_Qz,_QA,_QB){var _QC=new T(function(){var _QD=E(_Qz);if(!_QD[0]){return false;}else{if(!E(_QD[1])){return false;}else{return true;}}}),_QE=new T(function(){var _QF=E(_Qy);if(!_QF[0]){return [0];}else{var _QG=E(_QF[1]),_QH=B(_b7(_QA,0))+B(_b7(_QB,0))|0;if(_QH>=_QG){return [0];}else{var _QI=_QG-_QH|0;if(0>=_QI){return [0];}else{var _QJ=new T(function(){if(!E(_QC)){return E(_Qw);}else{return E(_Qv);}}),_QK=function(_QL){var _QM=E(_QL);return (_QM==1)?[1,_QJ,_1l]:[1,_QJ,new T(function(){return B(_QK(_QM-1|0));})];};return B(_QK(_QI));}}}}),_QN=function(_QO){if(!E(_QC)){return new F(function(){return _16(_QE,new T(function(){return B(_16(_QA,_QB));},1));});}else{return new F(function(){return _16(_QA,new T(function(){return B(_16(_QE,_QB));},1));});}},_QP=E(_Qz);if(!_QP[0]){return new F(function(){return _QN(_);});}else{if(!E(_QP[1])){return new F(function(){return _16(_QA,new T(function(){return B(_16(_QB,_QE));},1));});}else{return new F(function(){return _QN(_);});}}},_QQ=function(_QR,_QS,_QT,_QU,_QV){var _QW=E(_QT);if(!_QW[0]){return new F(function(){return _Qx(_QR,_QS,_QU,_QV);});}else{if(!E(_QW[1])){var _QX=E(_QU);if(!_QX[0]){return new F(function(){return _Qx(_QR,_QS,_Qu,_QV);});}else{return new F(function(){return _Qx(_QR,_QS,_QX,_QV);});}}else{var _QY=E(_QU);if(!_QY[0]){return new F(function(){return _Qx(_QR,_QS,_Qt,_QV);});}else{return new F(function(){return _Qx(_QR,_QS,_QY,_QV);});}}}},_QZ=function(_R0,_R1,_R2,_R3,_R4,_R5,_R6){var _R7=E(_R6);switch(_R7){case 69:var _R8=new T(function(){var _R9=B(_Qf(69,_R2,_R5,_R0));return B(_QQ(_R1,_R3,_R4,_R9[1],_R9[2]));});return function(_lz){return new F(function(){return _16(_R8,_lz);});};case 70:var _Ra=new T(function(){var _Rb=B(_Qf(70,_R2,_R5,_R0));return B(_QQ(_R1,_R3,_R4,_Rb[1],_Rb[2]));});return function(_lz){return new F(function(){return _16(_Ra,_lz);});};case 71:var _Rc=new T(function(){var _Rd=B(_Qf(71,_R2,_R5,_R0));return B(_QQ(_R1,_R3,_R4,_Rd[1],_Rd[2]));});return function(_lz){return new F(function(){return _16(_Rc,_lz);});};case 101:var _Re=new T(function(){var _Rf=B(_Qf(101,_R2,_R5,_R0));return B(_QQ(_R1,_R3,_R4,_Rf[1],_Rf[2]));});return function(_lz){return new F(function(){return _16(_Re,_lz);});};case 102:var _Rg=new T(function(){var _Rh=B(_Qf(102,_R2,_R5,_R0));return B(_QQ(_R1,_R3,_R4,_Rh[1],_Rh[2]));});return function(_lz){return new F(function(){return _16(_Rg,_lz);});};case 103:var _Ri=new T(function(){var _Rj=B(_Qf(103,_R2,_R5,_R0));return B(_QQ(_R1,_R3,_R4,_Rj[1],_Rj[2]));});return function(_lz){return new F(function(){return _16(_Ri,_lz);});};case 118:var _Rk=new T(function(){var _Rl=B(_Qf(103,_R2,_R5,_R0));return B(_QQ(_R1,_R3,_R4,_Rl[1],_Rl[2]));});return function(_lz){return new F(function(){return _16(_Rk,_lz);});};default:return new F(function(){return _yz(_R7);});}},_Rm=function(_Rn,_Ro){var _Rp=E(_Ro);return new F(function(){return _QZ(_Rn,_Rp[1],_Rp[2],_Rp[3],_Rp[4],_Rp[5],E(_Rp[7]));});},_Rq=function(_Rr){return E(_Rr);},_Rs=new T(function(){return B(unCStr("printf: argument list ended prematurely"));}),_Rt=new T(function(){return B(err(_Rs));}),_Ru=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_Rv=new T(function(){return B(err(_Ru));}),_Rw=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_Rx=new T(function(){return B(err(_Rw));}),_Ry=function(_Rz,_RA){var _RB=function(_RC,_RD){var _RE=function(_RF){return new F(function(){return A(_RD,[new T(function(){return  -E(_RF);})]);});},_RG=new T(function(){return B(_jm(function(_RH){return new F(function(){return A(_Rz,[_RH,_RC,_RE]);});}));}),_RI=function(_RJ){return E(_RG);},_RK=function(_RL){return new F(function(){return A(_i3,[_RL,_RI]);});},_RM=new T(function(){return B(_jm(function(_RN){var _RO=E(_RN);if(_RO[0]==4){var _RP=E(_RO[1]);if(!_RP[0]){return new F(function(){return A(_Rz,[_RO,_RC,_RD]);});}else{if(E(_RP[1])==45){if(!E(_RP[2])[0]){return [1,_RK];}else{return new F(function(){return A(_Rz,[_RO,_RC,_RD]);});}}else{return new F(function(){return A(_Rz,[_RO,_RC,_RD]);});}}}else{return new F(function(){return A(_Rz,[_RO,_RC,_RD]);});}}));}),_RQ=function(_RR){return E(_RM);};return [1,function(_RS){return new F(function(){return A(_i3,[_RS,_RQ]);});}];};return new F(function(){return _kd(_RB,_RA);});},_RT=function(_RU){var _RV=E(_RU);if(!_RV[0]){var _RW=_RV[2];return [1,new T(function(){return B(_bA(new T(function(){return B(_bg(E(_RV[1])));}),new T(function(){return B(_b7(_RW,0));},1),B(_bc(_bi,_RW))));})];}else{return (E(_RV[2])[0]==0)?(E(_RV[3])[0]==0)?[1,new T(function(){return B(_bQ(_b6,_RV[1]));})]:[0]:[0];}},_RX=function(_RY,_RZ){return [2];},_S0=function(_S1){var _S2=E(_S1);if(_S2[0]==5){var _S3=B(_RT(_S2[1]));if(!_S3[0]){return E(_RX);}else{var _S4=new T(function(){return B(_cK(_S3[1]));});return function(_S5,_S6){return new F(function(){return A(_S6,[_S4]);});};}}else{return E(_RX);}},_S7=function(_S8){var _S9=function(_Sa){return [3,_S8,_8Y];};return [1,function(_Sb){return new F(function(){return A(_i3,[_Sb,_S9]);});}];},_Sc=new T(function(){return B(A(_Ry,[_S0,_jT,_S7]));}),_Sd=100,_Se=[0,_6J,_6J,_6J,_6J,_cx,_1l,_Sd],_Sf=function(_Sg){while(1){var _Sh=B((function(_Si){var _Sj=E(_Si);if(!_Sj[0]){return [0];}else{var _Sk=_Sj[2],_Sl=E(_Sj[1]);if(!E(_Sl[2])[0]){return [1,_Sl[1],new T(function(){return B(_Sf(_Sk));})];}else{_Sg=_Sk;return null;}}})(_Sg));if(_Sh!=null){return _Sh;}}},_Sm=function(_Sn){var _So=E(_Sn);if(!_So[0]){return E(_Rt);}else{var _Sp=new T(function(){var _Sq=B(_Sf(B(_7S(_Sc,new T(function(){return B(A(E(_So[1])[2],[_Se,_1l]));})))));if(!_Sq[0]){return E(_Rv);}else{if(!E(_Sq[2])[0]){return E(_Sq[1]);}else{return E(_Rx);}}});return [0,_So[2],_Sp];}},_Sr=function(_Ss){return (E(_Ss)-48|0)>>>0<=9;},_St=0,_Su=[1,_St],_Sv=0,_Sw=0,_Sx=[1,_Sw],_Sy=1,_Sz=[1,_Sy],_SA=new T(function(){var _SB=B(_7t(_Sr,_1l)),_SC=_SB[2],_SD=E(_SB[1]);if(!_SD[0]){return [0,_Sv,_SC];}else{return [0,new T(function(){var _SE=B(_Sf(B(_7S(_Sc,_SD))));if(!_SE[0]){return E(_Rv);}else{if(!E(_SE[2])[0]){return E(_SE[1]);}else{return E(_Rx);}}}),_SC];}}),_SF=new T(function(){return E(E(_SA)[1]);}),_SG=[1,_SF],_SH=new T(function(){return E(E(_SA)[2]);}),_SI=1,_SJ=[1,_SI],_SK=function(_SL,_SM,_SN,_SO,_SP,_SQ){while(1){var _SR=B((function(_SS,_ST,_SU,_SV,_SW,_SX){var _SY=E(_SW);if(!_SY[0]){return E(_wM);}else{var _SZ=_SY[2],_T0=E(_SY[1]);switch(_T0){case 32:var _T1=_SS,_T2=_ST,_T3=_SV,_T4=_SX;_SL=_T1;_SM=_T2;_SN=new T(function(){var _T5=E(_SU);if(!_T5[0]){return E(_Sz);}else{if(!E(_T5[1])){return E(_Sx);}else{return E(_Sz);}}});_SO=_T3;_SP=_SZ;_SQ=_T4;return null;case 35:var _T1=_SS,_T2=_ST,_T6=_SU,_T4=_SX;_SL=_T1;_SM=_T2;_SN=_T6;_SO=_cy;_SP=_SZ;_SQ=_T4;return null;case 42:var _T7=new T(function(){var _T8=B(_Sm(_SX));return [0,_T8[1],_T8[2]];}),_T9=new T(function(){var _Ta=E(_SZ);if(!_Ta[0]){return [0,_6J,_1l,new T(function(){return E(E(_T7)[1]);})];}else{if(E(_Ta[1])==46){var _Tb=E(_Ta[2]);if(!_Tb[0]){return [0,_SG,_SH,new T(function(){return E(E(_T7)[1]);})];}else{if(E(_Tb[1])==42){var _Tc=new T(function(){var _Td=B(_Sm(E(_T7)[1]));return [0,_Td[1],_Td[2]];});return [0,[1,new T(function(){return E(E(_Tc)[2]);})],_Tb[2],new T(function(){return E(E(_Tc)[1]);})];}else{var _Te=new T(function(){var _Tf=B(_7t(_Sr,_Tb)),_Tg=_Tf[2],_Th=E(_Tf[1]);if(!_Th[0]){return [0,_Sv,_Tg];}else{return [0,new T(function(){var _Ti=B(_Sf(B(_7S(_Sc,_Th))));if(!_Ti[0]){return E(_Rv);}else{if(!E(_Ti[2])[0]){return E(_Ti[1]);}else{return E(_Rx);}}}),_Tg];}});return [0,[1,new T(function(){return E(E(_Te)[1]);})],new T(function(){return E(E(_Te)[2]);}),new T(function(){return E(E(_T7)[1]);})];}}}else{return [0,_6J,_Ta,new T(function(){return E(E(_T7)[1]);})];}}}),_Tj=new T(function(){return E(E(_T9)[3]);}),_Tk=new T(function(){var _Tl=E(_Tj);if(!_Tl[0]){return E(_Rt);}else{return B(A(E(_Tl[1])[1],[new T(function(){return E(E(_T9)[2]);})]));}}),_Tm=new T(function(){return E(E(_T7)[2]);});return [0,[0,[1,new T(function(){return B(_H9(_Tm));})],new T(function(){return E(E(_T9)[1]);}),new T(function(){if(E(_Tm)>=0){if(!E(_SS)){if(!E(_ST)){return [0];}else{return E(_SJ);}}else{return E(_Su);}}else{return E(_Su);}}),_SU,_SV,new T(function(){return E(E(_Tk)[1]);}),new T(function(){return E(E(_Tk)[2]);})],new T(function(){return E(E(_Tk)[3]);}),_Tj];case 43:var _T1=_SS,_T2=_ST,_T3=_SV,_T4=_SX;_SL=_T1;_SM=_T2;_SN=_Sx;_SO=_T3;_SP=_SZ;_SQ=_T4;return null;case 45:var _T2=_ST,_T6=_SU,_T3=_SV,_T4=_SX;_SL=_cy;_SM=_T2;_SN=_T6;_SO=_T3;_SP=_SZ;_SQ=_T4;return null;case 46:var _Tn=new T(function(){var _To=E(_SZ);if(!_To[0]){var _Tp=B(_7t(_Sr,_1l)),_Tq=_Tp[2],_Tr=E(_Tp[1]);if(!_Tr[0]){return [0,_Sv,_Tq,_SX];}else{return [0,new T(function(){var _Ts=B(_Sf(B(_7S(_Sc,_Tr))));if(!_Ts[0]){return E(_Rv);}else{if(!E(_Ts[2])[0]){return E(_Ts[1]);}else{return E(_Rx);}}}),_Tq,_SX];}}else{if(E(_To[1])==42){var _Tt=new T(function(){var _Tu=B(_Sm(_SX));return [0,_Tu[1],_Tu[2]];});return [0,new T(function(){return E(E(_Tt)[2]);}),_To[2],new T(function(){return E(E(_Tt)[1]);})];}else{var _Tv=B(_7t(_Sr,_To)),_Tw=_Tv[2],_Tx=E(_Tv[1]);if(!_Tx[0]){return [0,_Sv,_Tw,_SX];}else{return [0,new T(function(){var _Ty=B(_Sf(B(_7S(_Sc,_Tx))));if(!_Ty[0]){return E(_Rv);}else{if(!E(_Ty[2])[0]){return E(_Ty[1]);}else{return E(_Rx);}}}),_Tw,_SX];}}}}),_Tz=new T(function(){return E(E(_Tn)[3]);}),_TA=new T(function(){var _TB=E(_Tz);if(!_TB[0]){return E(_Rt);}else{return B(A(E(_TB[1])[1],[new T(function(){return E(E(_Tn)[2]);})]));}});return [0,[0,_6J,[1,new T(function(){return E(E(_Tn)[1]);})],new T(function(){if(!E(_SS)){if(!E(_ST)){return [0];}else{return E(_SJ);}}else{return E(_Su);}}),_SU,_SV,new T(function(){return E(E(_TA)[1]);}),new T(function(){return E(E(_TA)[2]);})],new T(function(){return E(E(_TA)[3]);}),_Tz];case 48:var _T1=_SS,_T6=_SU,_T3=_SV,_T4=_SX;_SL=_T1;_SM=_cy;_SN=_T6;_SO=_T3;_SP=_SZ;_SQ=_T4;return null;default:if((_T0-48|0)>>>0>9){var _TC=new T(function(){var _TD=E(_SX);if(!_TD[0]){return E(_Rt);}else{return B(A(E(_TD[1])[1],[_SY]));}});return [0,[0,_6J,_6J,new T(function(){if(!E(_SS)){if(!E(_ST)){return [0];}else{return E(_SJ);}}else{return E(_Su);}}),_SU,_SV,new T(function(){return E(E(_TC)[1]);}),new T(function(){return E(E(_TC)[2]);})],new T(function(){return E(E(_TC)[3]);}),_SX];}else{var _TE=new T(function(){var _TF=B(_7t(_Sr,_SY)),_TG=_TF[2],_TH=E(_TF[1]);if(!_TH[0]){return [0,_Sv,_TG];}else{return [0,new T(function(){var _TI=B(_Sf(B(_7S(_Sc,_TH))));if(!_TI[0]){return E(_Rv);}else{if(!E(_TI[2])[0]){return E(_TI[1]);}else{return E(_Rx);}}}),_TG];}}),_TJ=new T(function(){var _TK=E(E(_TE)[2]);if(!_TK[0]){return [0,_6J,_1l,_SX];}else{if(E(_TK[1])==46){var _TL=E(_TK[2]);if(!_TL[0]){return [0,_SG,_SH,_SX];}else{if(E(_TL[1])==42){var _TM=new T(function(){var _TN=B(_Sm(_SX));return [0,_TN[1],_TN[2]];});return [0,[1,new T(function(){return E(E(_TM)[2]);})],_TL[2],new T(function(){return E(E(_TM)[1]);})];}else{var _TO=new T(function(){var _TP=B(_7t(_Sr,_TL)),_TQ=_TP[2],_TR=E(_TP[1]);if(!_TR[0]){return [0,_Sv,_TQ];}else{return [0,new T(function(){var _TS=B(_Sf(B(_7S(_Sc,_TR))));if(!_TS[0]){return E(_Rv);}else{if(!E(_TS[2])[0]){return E(_TS[1]);}else{return E(_Rx);}}}),_TQ];}});return [0,[1,new T(function(){return E(E(_TO)[1]);})],new T(function(){return E(E(_TO)[2]);}),_SX];}}}else{return [0,_6J,_TK,_SX];}}}),_TT=new T(function(){return E(E(_TJ)[3]);}),_TU=new T(function(){var _TV=E(_TT);if(!_TV[0]){return E(_Rt);}else{return B(A(E(_TV[1])[1],[new T(function(){return E(E(_TJ)[2]);})]));}}),_TW=new T(function(){return E(E(_TE)[1]);});return [0,[0,[1,new T(function(){return B(_H9(_TW));})],new T(function(){return E(E(_TJ)[1]);}),new T(function(){if(E(_TW)>=0){if(!E(_SS)){if(!E(_ST)){return [0];}else{return E(_SJ);}}else{return E(_Su);}}else{return E(_Su);}}),_SU,_SV,new T(function(){return E(E(_TU)[1]);}),new T(function(){return E(E(_TU)[2]);})],new T(function(){return E(E(_TU)[3]);}),_TT];}}}})(_SL,_SM,_SN,_SO,_SP,_SQ));if(_SR!=null){return _SR;}}},_TX=37,_TY=function(_TZ,_U0,_U1){var _U2=E(_TZ);if(!_U2[0]){return (E(_U0)[0]==0)?E(_U1):E(_wM);}else{var _U3=_U2[2],_U4=E(_U2[1]);if(E(_U4)==37){var _U5=function(_U6){var _U7=E(_U0);if(!_U7[0]){return E(_Rt);}else{var _U8=B(_SK(_cx,_cx,_6J,_cx,_U3,_U7)),_U9=E(_U8[3]);if(!_U9[0]){return E(_Rt);}else{return new F(function(){return A(E(_U9[1])[2],[_U8[1],new T(function(){return B(_TY(_U8[2],_U9[2],_U6));})]);});}}},_Ua=E(_U3);if(!_Ua[0]){return new F(function(){return _U5(_U1);});}else{if(E(_Ua[1])==37){return [1,_TX,new T(function(){return B(_TY(_Ua[2],_U0,_U1));})];}else{return new F(function(){return _U5(_U1);});}}}else{return [1,_U4,new T(function(){return B(_TY(_U3,_U0,_U1));})];}}},_Ub=function(_Uc,_Ud){return new F(function(){return _bc(_Rq,B(_TY(_Uc,new T(function(){return B(_sU(_Ud,_1l));},1),_1l)));});},_Ue=function(_Uf,_Ug,_Uh,_Ui,_Uj){if(_Ug!=_Ug){return new F(function(){return _rl(_Uf,_Ug,E(_Ui));});}else{return new F(function(){return _rl(_Uf,E(_Uh),E(_Uj));});}},_Uk=new T(function(){return B(unCStr("%.3f"));}),_Ul=32,_Um=new T(function(){return B(unCStr("ccdtrans sav"));}),_Un=new T(function(){return B(unCStr("  ccdacq_nodark"));}),_Uo=new T(function(){return B(unAppCStr("}",_wF));}),_Up=new T(function(){return B(_16(_wF,_Uo));}),_Uq=new T(function(){return B(unCStr("\""));}),_Ur=new T(function(){return B(_1g(0,1,_1l));}),_Us=new T(function(){return B(unCStr("1"));}),_Ut=new T(function(){return B(_16(_Us,_1l));}),_Uu=[1,_Ul,_Ut],_Uv=new T(function(){return B(_16(_Ur,_Uu));}),_Uw=[1,_Ul,_Uv],_Ux=new T(function(){var _Uy=jsShow(0);return fromJSStr(_Uy);}),_Uz=new T(function(){var _UA=jsShow(4.0e-2);return fromJSStr(_UA);}),_UB=function(_UC){return new F(function(){return _Ub(_Uk,[1,[0,function(_kQ){return new F(function(){return _wN(_UC,_kQ);});},function(_kQ){return new F(function(){return _Rm(_UC,_kQ);});}],_1l]);});},_UD=function(_UE,_UF,_UG,_UH){if(!E(_UE)){var _UI=new T(function(){var _UJ=new T(function(){var _UK=E(E(_UG)[1])[2],_UL=E(_UF);if(!E(_UL[6])){return E(_UL[3])+E(_UK)*25/900;}else{return E(_UL[4])+E(_UK)*25/900;}}),_UM=new T(function(){var _UN=new T(function(){var _UO=new T(function(){var _UP=E(_UF),_UQ=_UP[5],_UR=E(_UG),_US=E(_UR[1]),_UT=E(_US[1]),_UU=E(_UR[2]),_UV=_UU[1],_UW=B(_Ue(E(_UP[7]),_UT,_US[2],_UV,_UU[2])),_UX=new T(function(){var _UY=new T(function(){var _UZ=new T(function(){var _V0=new T(function(){var _V1=new T(function(){var _V2=new T(function(){var _V3=new T(function(){return E(_UQ)+12.5+(_UT*25/900-12.5)*Math.cos(E(_UH));}),_V4=new T(function(){var _V5=new T(function(){var _V6=new T(function(){return (E(_UQ)+12.5+(E(_UV)*25/900-12.5)*Math.cos(E(_UH))-E(_V3))/_UW;}),_V7=new T(function(){var _V8=new T(function(){var _V9=new T(function(){var _Va=new T(function(){return (_UT*25/900-12.5)*Math.sin(E(_UH));}),_Vb=new T(function(){var _Vc=new T(function(){var _Vd=new T(function(){return ((E(_UV)*25/900-12.5)*Math.sin(E(_UH))-E(_Va))/_UW;}),_Ve=new T(function(){var _Vf=new T(function(){var _Vg=new T(function(){var _Vh=new T(function(){var _Vi=new T(function(){var _Vj=new T(function(){var _Vk=new T(function(){var _Vl=new T(function(){return B(_16(B(unAppCStr("\"",new T(function(){return B(_16(_UR[3],_Uq));}))),_1l));});return B(_16(_Uz,[1,_Ul,_Vl]));});return B(_16(B(_16(_Un,[1,_Ul,_Vk])),_Up));},1);return B(_16(_wF,_Vj));});return B(unAppCStr("  umv tmp2 x",_Vi));},1);return B(_16(_wF,_Vh));});return B(unAppCStr("  umv sah y",_Vg));},1);return B(_16(_wF,_Vf));},1);return B(_16(B(_Ub(_Uk,[1,[0,function(_kQ){return new F(function(){return _wN(_Vd,_kQ);});},function(_kQ){return new F(function(){return _Rm(_Vd,_kQ);});}],_1l])),_Ve));});return B(unAppCStr("+i*",_Vc));},1);return B(_16(B(_UB(_Va)),_Vb));});return B(unAppCStr("  x = ",_V9));},1);return B(_16(_wF,_V8));},1);return B(_16(B(_Ub(_Uk,[1,[0,function(_kQ){return new F(function(){return _wN(_V6,_kQ);});},function(_kQ){return new F(function(){return _Rm(_V6,_kQ);});}],_1l])),_V7));});return B(unAppCStr("+i*",_V5));},1);return B(_16(B(_UB(_V3)),_V4));});return B(unAppCStr("  y = ",_V2));},1);return B(_16(_wF,_V1));});return B(unAppCStr("{",_V0));},1);return B(_16(_wF,_UZ));});return B(unAppCStr(";i+=1)",_UY));},1);return B(_16(B(_1g(0,_UW,_1l)),_UX));});return B(unAppCStr("for(i=0;i<=",_UO));},1);return B(_16(_wF,_UN));},1);return B(_16(B(_Ub(_Uk,[1,[0,function(_kQ){return new F(function(){return _wN(_UJ,_kQ);});},function(_kQ){return new F(function(){return _Rm(_UJ,_kQ);});}],_1l])),_UM));});return new F(function(){return unAppCStr("umv sav ",_UI);});}else{var _Vm=new T(function(){var _Vn=new T(function(){return E(E(_UF)[5])+12.5+(E(E(E(_UG)[1])[1])*25/900-12.5)*Math.cos(E(_UH));}),_Vo=new T(function(){var _Vp=new T(function(){var _Vq=new T(function(){return (E(E(E(_UG)[1])[1])*25/900-12.5)*Math.sin(E(_UH));}),_Vr=new T(function(){var _Vs=new T(function(){var _Vt=new T(function(){var _Vu=new T(function(){var _Vv=E(E(_UG)[1])[2],_Vw=E(_UF);if(!E(_Vw[6])){return E(_Vw[3])+E(_Vv)*25/900;}else{return E(_Vw[4])+E(_Vv)*25/900;}}),_Vx=new T(function(){var _Vy=new T(function(){var _Vz=E(E(_UG)[2])[2],_VA=E(_UF);if(!E(_VA[6])){return E(_VA[3])+E(_Vz)*25/900;}else{return E(_VA[4])+E(_Vz)*25/900;}}),_VB=new T(function(){var _VC=E(_UG),_VD=E(_VC[1]),_VE=E(_VC[2]),_VF=new T(function(){var _VG=new T(function(){var _VH=new T(function(){return B(_16(B(unAppCStr("\"",new T(function(){return B(_16(_VC[3],_Uq));}))),_Uw));});return B(_16(_Ux,[1,_Ul,_VH]));});return B(_16(_Uz,[1,_Ul,_VG]));});return B(_16(B(_1g(0,B(_Ue(E(E(_UF)[7]),E(_VD[1]),_VD[2],_VE[1],_VE[2])),_1l)),[1,_Ul,_VF]));});return B(_16(B(_Ub(_Uk,[1,[0,function(_kQ){return new F(function(){return _wN(_Vy,_kQ);});},function(_kQ){return new F(function(){return _Rm(_Vy,_kQ);});}],_1l])),[1,_Ul,_VB]));});return B(_16(B(_Ub(_Uk,[1,[0,function(_kQ){return new F(function(){return _wN(_Vu,_kQ);});},function(_kQ){return new F(function(){return _Rm(_Vu,_kQ);});}],_1l])),[1,_Ul,_Vx]));});return B(_16(_Um,[1,_Ul,_Vt]));},1);return B(_16(_wF,_Vs));},1);return B(_16(B(_Ub(_Uk,[1,[0,function(_kQ){return new F(function(){return _wN(_Vq,_kQ);});},function(_kQ){return new F(function(){return _Rm(_Vq,_kQ);});}],_1l])),_Vr));});return B(unAppCStr(" tmp2 ",_Vp));},1);return B(_16(B(_Ub(_Uk,[1,[0,function(_kQ){return new F(function(){return _wN(_Vn,_kQ);});},function(_kQ){return new F(function(){return _Rm(_Vn,_kQ);});}],_1l])),_Vo));});return new F(function(){return unAppCStr("umv sah ",_Vm);});}},_VI=function(_VJ,_VK,_VL,_VM,_VN,_VO,_VP){var _VQ=[0,_wB,_VJ,_VK,_VL,_VM,_VN,_VO,_VP],_VR=function(_VS){var _VT=new T(function(){var _VU=E(_VS),_VV=rintDouble(_VU*180/3.141592653589793),_VW=B(_rV(_VV)),_VX=_VW[1],_VY=_VW[2],_VZ=new T(function(){var _W0=new T(function(){var _W1=B(_bc(function(_W2){var _W3=E(_W2);if(E(E(_W3[1])[1])!=E(E(_W3[2])[1])){return new F(function(){return _UD(_wx,_VQ,_W3,_VU);});}else{return new F(function(){return _UD(_wy,_VQ,_W3,_VU);});}},B(_sU(_VJ,_1l))));if(!_W1[0]){return [0];}else{return B(_wC([1,_W1[1],new T(function(){return B(_wH(_wF,_W1[2]));})]));}},1);return B(_16(_wF,_W0));});if(_VY>=0){return B(_16(B(_wt(0,B(_sZ(_VX,_VY)),_1l)),_VZ));}else{var _W4=hs_uncheckedIShiftRA64(B(_sb(_VX)), -_VY);return B(_16(B(_wt(0,B(_s1(_W4)),_1l)),_VZ));}});return new F(function(){return unAppCStr("umv sar ",_VT);});},_W5=B(_bc(_VR,_VP));if(!_W5[0]){return [0];}else{return new F(function(){return _wC([1,_W5[1],new T(function(){return B(_wH(_wG,_W5[2]));})]);});}},_W6=(function(id){return document.getElementById(id);}),_W7=function(_W8,_W9){var _Wa=function(_){var _Wb=E(_W6)(E(_W9)),_Wc=__eq(_Wb,E(_pk));return (E(_Wc)==0)?[1,_Wb]:_6J;};return new F(function(){return A(_2,[_W8,_Wa]);});},_Wd=new T(function(){return B(unCStr("\n"));}),_We=function(_Wf,_Wg,_){var _Wh=jsWriteHandle(E(_Wf),toJSStr(E(_Wg)));return _a;},_Wi=function(_Wj,_Wk,_){var _Wl=E(_Wj),_Wm=jsWriteHandle(_Wl,toJSStr(E(_Wk)));return new F(function(){return _We(_Wl,_Wd,_);});},_Wn=34,_Wo=[1,_Wn,_1l],_Wp=new T(function(){return B(unCStr("\\\""));}),_Wq=function(_Wr,_Ws){var _Wt=E(_Wr);if(!_Wt[0]){return E(_Ws);}else{var _Wu=_Wt[2],_Wv=E(_Wt[1]);if(_Wv==34){return new F(function(){return _16(_Wp,new T(function(){return B(_Wq(_Wu,_Ws));},1));});}else{return new F(function(){return _yl(_Wv,new T(function(){return B(_Wq(_Wu,_Ws));}));});}}},_Ww=function(_){return new F(function(){return jsMkStdout();});},_Wx=new T(function(){return B(_pg(_Ww));}),_Wy=function(_Wz,_WA,_WB,_){var _WC=B(A(_W7,[_6R,new T(function(){return toJSStr(E(_Wz));},1),_])),_WD=E(_WC);if(!_WD[0]){var _WE=new T(function(){var _WF=new T(function(){return B(_16(_WA,new T(function(){return B(unAppCStr("on page element ",_Wz));},1)));});return B(_Wq(B(unAppCStr("Failed to set ",_WF)),_Wo));}),_WG=B(_Wi(_Wx,[1,_Wn,_WE],_));return _a;}else{var _WH=E(_pU)(E(_WD[1]),toJSStr(E(_WA)),toJSStr(E(_WB)));return _a;}},_WI=new T(function(){return encodeURIComponent;}),_WJ=new T(function(){return B(unCStr("data:text/plain;charset=utf-8,"));}),_WK=new T(function(){return B(unCStr("href"));}),_WL=function(_WM,_WN,_){var _WO=E(_WI)(toJSStr(_WN)),_WP=new T(function(){return B(_16(_WJ,new T(function(){var _WQ=String(_WO);return fromJSStr(_WQ);},1)));},1);return new F(function(){return _Wy(_WM,_WK,_WP,_);});},_WR="scans",_WS=new T(function(){return B(_W7(_6R,_WR));}),_WT=(function(ctx,rad){ctx.rotate(rad);}),_WU=function(_WV,_WW,_WX,_){var _WY=E(_v8)(_WX),_WZ=E(_WT)(_WX,E(_WV)),_X0=B(A(_WW,[_WX,_])),_X1=E(_v7)(_WX);return new F(function(){return _v6(_);});},_X2=(function(ctx,x,y){ctx.translate(x,y);}),_X3=function(_X4,_X5,_X6,_X7,_){var _X8=E(_v8)(_X7),_X9=E(_X2)(_X7,E(_X4),E(_X5)),_Xa=B(A(_X6,[_X7,_])),_Xb=E(_v7)(_X7);return new F(function(){return _v6(_);});},_Xc=function(_Xd,_Xe,_Xf,_Xg,_Xh,_Xi,_Xj,_Xk){return new F(function(){return Math.atan((Math.tan(B(_CB(new T(function(){return B(_BT(_Xg,_Xe));}),_Xf-_Xd))-1.5707963267948966)+Math.tan(B(_CB(new T(function(){return B(_BT(_Xi,_Xg));}),_Xh-_Xf)))+Math.tan(B(_CB(new T(function(){return B(_BT(_Xk,_Xi));}),_Xj-_Xh))+1.5707963267948966)+Math.tan(B(_CB(new T(function(){return B(_BT(_Xe,_Xk));}),_Xd-_Xj))-3.141592653589793))/4);});},_Xl=function(_Xm){return E(_Xm)/2;},_Xn=function(_Xo,_Xp,_Xq,_){var _Xr=E(_Xo);return new F(function(){return _X3(_Xr[1],_Xr[2],_Xp,E(_Xq),_);});},_Xs=function(_Xt,_Xu){var _Xv=new T(function(){var _Xw=E(_Xt),_Xx=E(E(_Xu)[2]),_Xy=E(_Xx[1]),_Xz=E(_Xy[1]),_XA=E(_Xy[2]),_XB=E(_Xx[2]),_XC=E(_XB[1]),_XD=E(_XB[2]),_XE=E(_Xx[3]),_XF=E(_XE[1]),_XG=E(_XE[2]),_XH=E(_Xx[4]),_XI=E(_XH[1]),_XJ=E(_XH[2]);return Math.sqrt(E(_Xw[1])*E(_Xw[2])/(0.5*(_Xz*_XJ+_XI*_XG+_XF*_XA-_Xz*_XG-_XF*_XJ-_XI*_XA)+0.5*(_XI*_XG+_XF*_XD+_XC*_XJ-_XI*_XD-_XC*_XG-_XF*_XJ)));}),_XK=new T(function(){var _XL=E(_Xt);return [0,new T(function(){return B(_Xl(_XL[1]));}),new T(function(){return B(_Xl(_XL[2]));})];}),_XM=new T(function(){var _XN=E(E(_Xu)[2]),_XO=E(_XN[1]),_XP=E(_XN[2]),_XQ=E(_XN[3]),_XR=E(_XN[4]);return  -B(_Xc(E(_XO[1]),_XO[2],E(_XP[1]),_XP[2],E(_XQ[1]),_XQ[2],E(_XR[1]),_XR[2]));}),_XS=new T(function(){var _XT=E(E(_Xu)[2]),_XU=E(_XT[1]),_XV=E(_XT[2]),_XW=E(_XT[3]),_XX=E(_XT[4]);return [0,new T(function(){return (E(_XU[1])+E(_XV[1])+E(_XW[1])+E(_XX[1]))/4/(-1);}),new T(function(){return (E(_XU[2])+E(_XV[2])+E(_XW[2])+E(_XX[2]))/4/(-1);})];}),_XY=function(_XZ,_Y0,_){var _Y1=E(_XK),_Y2=function(_Y3,_){var _Y4=function(_Y5,_){return new F(function(){return _WU(_XM,function(_Y6,_){return new F(function(){return _Xn(_XS,_XZ,_Y6,_);});},E(_Y5),_);});};return new F(function(){return _va(_Xv,_Xv,_Y4,E(_Y3),_);});};return new F(function(){return _X3(_Y1[1],_Y1[2],_Y2,E(_Y0),_);});};return E(_XY);},_Y7=(function(ctx,x,y){ctx.moveTo(x,y);}),_Y8=(function(ctx,x,y){ctx.lineTo(x,y);}),_Y9=function(_Ya,_Yb,_){var _Yc=E(_Ya);if(!_Yc[0]){return _a;}else{var _Yd=E(_Yc[1]),_Ye=E(_Yb),_Yf=E(_Y7)(_Ye,E(_Yd[1]),E(_Yd[2])),_Yg=E(_Yc[2]);if(!_Yg[0]){return _a;}else{var _Yh=E(_Yg[1]),_Yi=E(_Y8),_Yj=_Yi(_Ye,E(_Yh[1]),E(_Yh[2])),_Yk=_Yg[2];while(1){var _Yl=E(_Yk);if(!_Yl[0]){return _a;}else{var _Ym=E(_Yl[1]),_Yn=_Yi(_Ye,E(_Ym[1]),E(_Ym[2]));_Yk=_Yl[2];continue;}}}}},_Yo=function(_Yp,_Yq,_){var _Yr=new T(function(){return E(E(_Yp)[2]);}),_Ys=new T(function(){return E(E(_Yr)[1]);});return new F(function(){return _Y9([1,_Ys,[1,new T(function(){return E(E(_Yr)[2]);}),[1,new T(function(){return E(E(_Yr)[3]);}),[1,new T(function(){return E(E(_Yr)[4]);}),[1,_Ys,_1l]]]]],_Yq,_);});},_Yt=(function(e){e.width = e.width;}),_Yu=",",_Yv="rgba(",_Yw=new T(function(){return toJSStr(_1l);}),_Yx="rgb(",_Yy=")",_Yz=[1,_Yy,_1l],_YA=function(_YB){var _YC=E(_YB);if(!_YC[0]){var _YD=jsCat([1,_Yx,[1,new T(function(){return String(_YC[1]);}),[1,_Yu,[1,new T(function(){return String(_YC[2]);}),[1,_Yu,[1,new T(function(){return String(_YC[3]);}),_Yz]]]]]],E(_Yw));return E(_YD);}else{var _YE=jsCat([1,_Yv,[1,new T(function(){return String(_YC[1]);}),[1,_Yu,[1,new T(function(){return String(_YC[2]);}),[1,_Yu,[1,new T(function(){return String(_YC[3]);}),[1,_Yu,[1,new T(function(){return String(_YC[4]);}),_Yz]]]]]]]],E(_Yw));return E(_YE);}},_YF="strokeStyle",_YG="fillStyle",_YH=(function(e,p){return e[p].toString();}),_YI=function(_YJ,_YK){var _YL=new T(function(){return B(_YA(_YJ));});return function(_YM,_){var _YN=E(_YM),_YO=E(_YG),_YP=E(_YH),_YQ=_YP(_YN,_YO),_YR=E(_YF),_YS=_YP(_YN,_YR),_YT=E(_YL),_YU=E(_1),_YV=_YU(_YN,_YO,_YT),_YW=_YU(_YN,_YR,_YT),_YX=B(A(_YK,[_YN,_])),_YY=String(_YQ),_YZ=_YU(_YN,_YO,_YY),_Z0=String(_YS),_Z1=_YU(_YN,_YR,_Z0);return new F(function(){return _v6(_);});};},_Z2=function(_Z3,_Z4,_Z5){var _Z6=E(_Z5);if(!_Z6[0]){return [0];}else{var _Z7=_Z6[1],_Z8=_Z6[2];return (!B(A(_Z3,[_Z4,_Z7])))?[1,_Z7,new T(function(){return B(_Z2(_Z3,_Z4,_Z8));})]:E(_Z8);}},_Z9="lineWidth",_Za=function(_Zb,_Zc){var _Zd=new T(function(){return String(E(_Zb));});return function(_Ze,_){var _Zf=E(_Ze),_Zg=E(_Z9),_Zh=E(_YH)(_Zf,_Zg),_Zi=E(_1),_Zj=_Zi(_Zf,_Zg,E(_Zd)),_Zk=B(A(_Zc,[_Zf,_])),_Zl=String(_Zh),_Zm=_Zi(_Zf,_Zg,_Zl);return new F(function(){return _v6(_);});};},_Zn=1,_Zo=0.2,_Zp=900,_Zq=[0,_Zp,_Zp],_Zr=new T(function(){return B(unCStr("saveLink"));}),_Zs=new T(function(){return B(unCStr("exportLink"));}),_Zt=new T(function(){return B(unCStr(" disabled"));}),_Zu=new T(function(){return B(unCStr("class"));}),_Zv="aligned",_Zw=new T(function(){return B(unCStr("page missing element for update"));}),_Zx=[1,_Wn,_1l],_Zy=new T(function(){return B(_Wq(_Zw,_Zx));}),_Zz=[1,_Wn,_Zy],_ZA="original",_ZB=[0,255,0,255],_ZC=function(_ZD,_ZE,_){while(1){var _ZF=E(_ZD);if(!_ZF[0]){return _a;}else{var _ZG=E(_ZF[1]),_ZH=B(_Y9([1,_ZG[1],[1,_ZG[2],_1l]],_ZE,_));_ZD=_ZF[2];continue;}}},_ZI=[0,255,0,255],_ZJ=1,_ZK=function(_ZL){var _ZM=new T(function(){var _ZN=function(_lz,_ZO){return new F(function(){return _ZC(E(_ZL)[2],_lz,_ZO);});};return B(_YI(_ZI,function(_ZP,_){return new F(function(){return _vl(_ZN,E(_ZP),_);});}));});return new F(function(){return _Za(_ZJ,_ZM);});},_ZQ=function(_ZR){while(1){var _ZS=E(_ZR);if(!_ZS[0]){return false;}else{var _ZT=E(_ZS[1]);if(!_ZT[0]){return true;}else{if(!B(_cp(_8D,_Ul,_ZT))){_ZR=_ZS[2];continue;}else{return true;}}}}},_ZU=function(_ZV){return E(E(_ZV)[3]);},_ZW=function(_ZX){return new F(function(){return fromJSStr(E(_ZX));});},_ZY=function(_ZZ,_100,_101,_102){var _103=new T(function(){var _104=function(_){var _105=E(_YH)(B(A(_pS,[_ZZ,_101])),E(_102));return new T(function(){return String(_105);});};return E(_104);});return new F(function(){return A(_2,[_100,_103]);});},_106=function(_107,_108,_109,_10a){var _10b=B(_pN(_108)),_10c=new T(function(){return B(_mG(_10b));}),_10d=function(_10e){return new F(function(){return A(_10c,[new T(function(){return B(_ZW(_10e));})]);});},_10f=new T(function(){return B(_ZY(_107,_108,_109,new T(function(){return toJSStr(E(_10a));},1)));});return new F(function(){return A(_mE,[_10b,_10f,_10d]);});},_10g=new T(function(){return B(unCStr("value"));}),_10h=function(_10i,_10j,_10k){var _10l=E(_10k);if(!_10l[0]){return [0];}else{var _10m=_10l[1],_10n=_10l[2];return (!B(A(_10i,[_10m])))?[1,_10m,new T(function(){return B(_10h(_10i,_10j,_10n));})]:[1,new T(function(){return B(A(_10j,[_10m]));}),new T(function(){return B(_10h(_10i,_10j,_10n));})];}},_10o=function(_10p,_10q,_10r,_10s,_){var _10t=B(A(_106,[_S,_6R,_10r,_10g,_])),_10u=_10t,_10v=E(_10q),_10w=rMV(_10v),_10x=E(_10w),_10y=new T(function(){return B(_10h(function(_10z){return new F(function(){return _nu(_10z,_10s);});},function(_10A){var _10B=E(_10A);return [0,_10B[1],_10B[2],_10u];},_10x[2]));}),_=wMV(_10v,[0,_10x[1],_10y,_10x[3],_10x[4],_10x[5],_10x[6],_10x[7],_10x[8]]);return new F(function(){return A(_10p,[_]);});},_10C=function(_10D,_10E,_10F,_){var _10G=rMV(_10E),_10H=_10G,_10I=E(_10D),_10J=rMV(_10I),_10K=new T(function(){return B(unAppCStr("btn btn-primary",new T(function(){var _10L=E(_10J),_10M=E(_10L[2]);if(!_10M[0]){return E(_Zt);}else{if(!B(_ZQ(B(_bc(_ZU,_10M))))){if(!E(_10L[8])[0]){return E(_Zt);}else{return [0];}}else{return E(_Zt);}}})));},1),_10N=B(_Wy(_Zs,_Zu,_10K,_)),_10O=E(_10J),_10P=B(_WL(_Zs,B(_VI(_10O[2],_10O[3],_10O[4],_10O[5],_10O[6],_10O[7],_10O[8])),_)),_10Q=B(_WL(_Zr,fromJSStr(B(_wa([4,E(B(_oi(_nE,[1,new T(function(){return [4,E(B(_nW(_10H)))];}),[1,new T(function(){return [4,E(B(_on(_10O)))];}),_1l]])))]))),_)),_10R=B(A(_W7,[_6R,_ZA,_])),_10S=E(_10R);if(!_10S[0]){var _10T=B(_Wi(_Wx,_Zz,_));return _a;}else{var _10U=E(_10S[1]),_10V=E(_N),_10W=_10V(_10U);if(!_10W){var _10X=B(_Wi(_Wx,_Zz,_));return _a;}else{var _10Y=E(_M),_10Z=_10Y(_10U),_110=_10Z,_111=B(A(_W7,[_6R,_Zv,_])),_112=function(_,_113){var _114=E(_113);if(!_114[0]){var _115=B(_Wi(_Wx,_Zz,_));return _a;}else{var _116=B(A(_WS,[_])),_117=E(_116);if(!_117[0]){var _118=B(_Wi(_Wx,_Zz,_));return _a;}else{var _119=function(_11a,_){var _11b=rMV(_10I),_11c=E(_11b),_=wMV(_10I,[0,_11c[1],new T(function(){return B(_Z2(_nu,_11a,_11c[2]));}),_11c[3],_11c[4],_11c[5],_11c[6],_11c[7],_11c[8]]);return new F(function(){return _10C(_10I,_10E,_10F,_);});},_11d=function(_){return new F(function(){return _10C(_10I,_10E,_10F,_);});},_11e=B(_t3(function(_n7,_mZ,_){return new F(function(){return _10o(_11d,_10I,_n7,_mZ,_);});},_119,_10O,E(_117[1]),_)),_11f=E(_10F),_11g=rMV(_11f),_11h=_11g,_11i=E(_114[1]),_11j=_11i[1],_11k=E(_Yt),_11l=_11k(_11i[2]),_11m=function(_11n,_){return new F(function(){return _vs(E(_11h),0,0,E(_11n),_);});},_11o=B(A(_Xs,[_Zq,_10H,function(_11p,_){return new F(function(){return _va(_Zo,_Zo,_11m,E(_11p),_);});},_11j,_])),_11q=B(A(_ZK,[_10O,_11j,_])),_11r=rMV(_11f),_11s=_11r,_11t=_11k(_10U),_11u=B(_va(_Zo,_Zo,function(_11v,_){return new F(function(){return _vs(E(_11s),0,0,E(_11v),_);});},_110,_)),_11w=new T(function(){var _11x=function(_mZ,_){return new F(function(){return _Yo(_10H,_mZ,_);});};return B(_YI(_ZB,function(_11y,_){return new F(function(){return _vl(_11x,E(_11y),_);});}));}),_11z=B(A(_Za,[_Zn,_11w,_110,_]));return _a;}}},_11A=E(_111);if(!_11A[0]){return new F(function(){return _112(_,_6J);});}else{var _11B=E(_11A[1]),_11C=_10V(_11B);if(!_11C){return new F(function(){return _112(_,_6J);});}else{var _11D=_10Y(_11B);return new F(function(){return _112(_,[1,[0,_11D,_11B]]);});}}}}},_11E=2,_11F="offset",_11G=new T(function(){return B(_W7(_6R,_11F));}),_11H="bottom",_11I=new T(function(){return B(_W7(_6R,_11H));}),_11J="top",_11K=new T(function(){return B(_W7(_6R,_11J));}),_11L=function(_11M,_11N){var _11O=function(_11P,_11Q){var _11R=function(_11S){return new F(function(){return A(_11Q,[new T(function(){return  -E(_11S);})]);});},_11T=new T(function(){return B(_jm(function(_11U){return new F(function(){return A(_11M,[_11U,_11P,_11R]);});}));}),_11V=function(_11W){return E(_11T);},_11X=function(_11Y){return new F(function(){return A(_i3,[_11Y,_11V]);});},_11Z=new T(function(){return B(_jm(function(_120){var _121=E(_120);if(_121[0]==4){var _122=E(_121[1]);if(!_122[0]){return new F(function(){return A(_11M,[_121,_11P,_11Q]);});}else{if(E(_122[1])==45){if(!E(_122[2])[0]){return [1,_11X];}else{return new F(function(){return A(_11M,[_121,_11P,_11Q]);});}}else{return new F(function(){return A(_11M,[_121,_11P,_11Q]);});}}}else{return new F(function(){return A(_11M,[_121,_11P,_11Q]);});}}));}),_123=function(_124){return E(_11Z);};return [1,function(_125){return new F(function(){return A(_i3,[_125,_123]);});}];};return new F(function(){return _kd(_11O,_11N);});},_126=new T(function(){return 1/0;}),_127=function(_128,_129){return new F(function(){return A(_129,[_126]);});},_12a=new T(function(){return 0/0;}),_12b=function(_12c,_12d){return new F(function(){return A(_12d,[_12a]);});},_12e=new T(function(){return B(unCStr("NaN"));}),_12f=new T(function(){return B(unCStr("Infinity"));}),_12g=function(_12h,_12i){while(1){var _12j=E(_12h);if(!_12j[0]){var _12k=E(_12j[1]);if(_12k==(-2147483648)){_12h=[1,I_fromInt(-2147483648)];continue;}else{var _12l=E(_12i);if(!_12l[0]){return [0,_12k%_12l[1]];}else{_12h=[1,I_fromInt(_12k)];_12i=_12l;continue;}}}else{var _12m=_12j[1],_12n=E(_12i);return (_12n[0]==0)?[1,I_rem(_12m,I_fromInt(_12n[1]))]:[1,I_rem(_12m,_12n[1])];}}},_12o=function(_12p,_12q){if(!B(_zK(_12q,_In))){return new F(function(){return _12g(_12p,_12q);});}else{return E(_zF);}},_12r=function(_12s,_12t){while(1){if(!B(_zK(_12t,_In))){var _12u=_12t,_12v=B(_12o(_12s,_12t));_12s=_12u;_12t=_12v;continue;}else{return E(_12s);}}},_12w=function(_12x){var _12y=E(_12x);if(!_12y[0]){var _12z=E(_12y[1]);return (_12z==(-2147483648))?E(_b1):(_12z<0)?[0, -_12z]:E(_12y);}else{var _12A=_12y[1];return (I_compareInt(_12A,0)>=0)?E(_12y):[1,I_negate(_12A)];}},_12B=5,_12C=new T(function(){return B(_zC(_12B));}),_12D=new T(function(){return die(_12C);}),_12E=function(_12F,_12G){if(!B(_zK(_12G,_In))){var _12H=B(_12r(B(_12w(_12F)),B(_12w(_12G))));return (!B(_zK(_12H,_In)))?[0,B(_MN(_12F,_12H)),B(_MN(_12G,_12H))]:E(_zF);}else{return E(_12D);}},_12I=new T(function(){return B(_zK(_Io,_In));}),_12J=function(_12K,_12L,_12M){while(1){if(!E(_12I)){if(!B(_zK(B(_12g(_12L,_Io)),_In))){if(!B(_zK(_12L,_F5))){var _12N=B(_bm(_12K,_12K)),_12O=B(_MN(B(_AT(_12L,_F5)),_Io)),_12P=B(_bm(_12K,_12M));_12K=_12N;_12L=_12O;_12M=_12P;continue;}else{return new F(function(){return _bm(_12K,_12M);});}}else{var _12N=B(_bm(_12K,_12K)),_12O=B(_MN(_12L,_Io));_12K=_12N;_12L=_12O;continue;}}else{return E(_zF);}}},_12Q=function(_12R,_12S){while(1){if(!E(_12I)){if(!B(_zK(B(_12g(_12S,_Io)),_In))){if(!B(_zK(_12S,_F5))){return new F(function(){return _12J(B(_bm(_12R,_12R)),B(_MN(B(_AT(_12S,_F5)),_Io)),_12R);});}else{return E(_12R);}}else{var _12T=B(_bm(_12R,_12R)),_12U=B(_MN(_12S,_Io));_12R=_12T;_12S=_12U;continue;}}else{return E(_zF);}}},_12V=function(_12W,_12X){if(!B(_wk(_12X,_In))){if(!B(_zK(_12X,_In))){return new F(function(){return _12Q(_12W,_12X);});}else{return E(_F5);}}else{return E(_J4);}},_12Y=[0,1],_12Z=[0,0],_130=[0,-1],_131=function(_132){var _133=E(_132);if(!_133[0]){var _134=_133[1];return (_134>=0)?(E(_134)==0)?E(_12Z):E(_aQ):E(_130);}else{var _135=I_compareInt(_133[1],0);return (_135<=0)?(E(_135)==0)?E(_12Z):E(_130):E(_aQ);}},_136=function(_137,_138,_139){while(1){var _13a=E(_139);if(!_13a[0]){if(!B(_wk(_137,_bz))){return [0,B(_bm(_138,B(_12V(_b6,_137)))),_F5];}else{var _13b=B(_12V(_b6,B(_b2(_137))));return new F(function(){return _12E(B(_bm(_138,B(_131(_13b)))),B(_12w(_13b)));});}}else{var _13c=B(_AT(_137,_12Y)),_13d=B(_aS(B(_bm(_138,_b6)),B(_bg(E(_13a[1])))));_137=_13c;_138=_13d;_139=_13a[2];continue;}}},_13e=function(_13f,_13g){var _13h=E(_13f);if(!_13h[0]){var _13i=_13h[1],_13j=E(_13g);return (_13j[0]==0)?_13i>=_13j[1]:I_compareInt(_13j[1],_13i)<=0;}else{var _13k=_13h[1],_13l=E(_13g);return (_13l[0]==0)?I_compareInt(_13k,_13l[1])>=0:I_compare(_13k,_13l[1])>=0;}},_13m=function(_13n){var _13o=E(_13n);if(!_13o[0]){var _13p=_13o[2];return new F(function(){return _12E(B(_bm(B(_bA(new T(function(){return B(_bg(E(_13o[1])));}),new T(function(){return B(_b7(_13p,0));},1),B(_bc(_bi,_13p)))),_12Y)),_12Y);});}else{var _13q=_13o[1],_13r=_13o[3],_13s=E(_13o[2]);if(!_13s[0]){var _13t=E(_13r);if(!_13t[0]){return new F(function(){return _12E(B(_bm(B(_bQ(_b6,_13q)),_12Y)),_12Y);});}else{var _13u=_13t[1];if(!B(_13e(_13u,_bz))){var _13v=B(_12V(_b6,B(_b2(_13u))));return new F(function(){return _12E(B(_bm(B(_bQ(_b6,_13q)),B(_131(_13v)))),B(_12w(_13v)));});}else{return new F(function(){return _12E(B(_bm(B(_bm(B(_bQ(_b6,_13q)),B(_12V(_b6,_13u)))),_12Y)),_12Y);});}}}else{var _13w=_13s[1],_13x=E(_13r);if(!_13x[0]){return new F(function(){return _136(_bz,B(_bQ(_b6,_13q)),_13w);});}else{return new F(function(){return _136(_13x[1],B(_bQ(_b6,_13q)),_13w);});}}}},_13y=function(_13z,_13A){while(1){var _13B=E(_13A);if(!_13B[0]){return [0];}else{if(!B(A(_13z,[_13B[1]]))){return E(_13B);}else{_13A=_13B[2];continue;}}}},_13C=0,_13D=function(_13E){return new F(function(){return _Hn(_13C,_13E);});},_13F=[0,E(_bz),E(_F5)],_13G=[1,_13F],_13H=[0,-2147483648],_13I=[0,2147483647],_13J=function(_13K,_13L,_13M){var _13N=E(_13M);if(!_13N[0]){return [1,new T(function(){var _13O=B(_13m(_13N));return [0,E(_13O[1]),E(_13O[2])];})];}else{var _13P=E(_13N[3]);if(!_13P[0]){return [1,new T(function(){var _13Q=B(_13m(_13N));return [0,E(_13Q[1]),E(_13Q[2])];})];}else{var _13R=_13P[1];if(!B(_A8(_13R,_13I))){if(!B(_wk(_13R,_13H))){var _13S=function(_13T){var _13U=_13T+B(_cK(_13R))|0;return (_13U<=(E(_13L)+3|0))?(_13U>=(E(_13K)-3|0))?[1,new T(function(){var _13V=B(_13m(_13N));return [0,E(_13V[1]),E(_13V[2])];})]:E(_13G):[0];},_13W=B(_13y(_13D,_13N[1]));if(!_13W[0]){var _13X=E(_13N[2]);if(!_13X[0]){return E(_13G);}else{var _13Y=B(_7t(_13D,_13X[1]));if(!E(_13Y[2])[0]){return E(_13G);}else{return new F(function(){return _13S( -B(_b7(_13Y[1],0)));});}}}else{return new F(function(){return _13S(B(_b7(_13W,0)));});}}else{return [0];}}else{return [0];}}}},_13Z=function(_140){var _141=E(_140);switch(_141[0]){case 3:var _142=_141[1];return (!B(_2b(_142,_12f)))?(!B(_2b(_142,_12e)))?E(_RX):E(_12b):E(_127);case 5:var _143=B(_13J(_Dj,_Di,_141[1]));if(!_143[0]){return E(_127);}else{var _144=new T(function(){var _145=E(_143[1]);return B(_BA(_145[1],_145[2]));});return function(_146,_147){return new F(function(){return A(_147,[_144]);});};}break;default:return E(_RX);}},_148=function(_m8){return new F(function(){return _11L(_13Z,_m8);});},_149=function(_14a,_14b){return new F(function(){return _kS(_148,_14b);});},_14c=function(_14d){var _14e=new T(function(){return B(A(_11L,[_13Z,_14d,_8Z]));});return function(_lz){return new F(function(){return _7S(_14e,_lz);});};},_14f=new T(function(){return B(_kS(_148,_8Z));}),_14g=function(_m8){return new F(function(){return _7S(_14f,_m8);});},_14h=[0,_14c,_14g,_148,_149],_14i=new T(function(){return B(unCStr("value"));}),_14j=34,_14k=new T(function(){return B(unCStr("do not use readS_to_P in gather!"));}),_14l=new T(function(){return B(err(_14k));}),_14m=function(_14n,_14o){var _14p=E(_14o);switch(_14p[0]){case 0:return [0,function(_14q){return new F(function(){return _14m(function(_14r){return new F(function(){return A(_14n,[[1,_14q,_14r]]);});},B(A(_14p[1],[_14q])));});}];case 1:return [1,function(_14s){return new F(function(){return _14m(_14n,B(A(_14p[1],[_14s])));});}];case 2:return [2];case 3:return new F(function(){return _82(B(A(_14p[1],[new T(function(){return B(A(_14n,[_1l]));})])),new T(function(){return B(_14m(_14n,_14p[2]));}));});break;default:return E(_14l);}},_14t=[3,_8Z,_8Y],_14u=function(_14v){return E(_14t);},_14w=new T(function(){return B(_jm(_14u));}),_14x=new T(function(){return B(_14m(_Q,_14w));}),_14y=function(_14z){return E(_14x);},_14A=function(_14B){return new F(function(){return A(_i3,[_14B,_14y]);});},_14C=[1,_14A],_14D=function(_14E){var _14F=E(_14E);if(!_14F[0]){return [0];}else{var _14G=E(_14F[1]),_14H=new T(function(){return B(_14D(_14F[2]));}),_14I=function(_14J){while(1){var _14K=B((function(_14L){var _14M=E(_14L);if(!_14M[0]){return E(_14H);}else{var _14N=_14M[2],_14O=E(_14M[1]);if(!E(_14O[1])[0]){if(!E(_14O[2])[0]){return [1,_14G[1],new T(function(){return B(_14I(_14N));})];}else{_14J=_14N;return null;}}else{_14J=_14N;return null;}}})(_14J));if(_14K!=null){return _14K;}}};return new F(function(){return _14I(B(_7S(_14C,_14G[2])));});}},_14P=new T(function(){return B(unCStr("\""));}),_14Q=new T(function(){return B(unCStr("...\""));}),_14R=12,_14S=function(_14T){return E(E(_14T)[1]);},_14U=function(_14V,_14W){var _14X=new T(function(){var _14Y=B(_Ol(_14R,_14W));return B(_16(_14Y[1],new T(function(){if(B(_b7(_14W,0))>15){return E(_14Q);}else{return B(_16(_14Y[2],_14P));}},1)));}),_14Z=B(_14D(B(A(_14S,[_14V,_jT,_14W]))));return (_14Z[0]==0)?[0,new T(function(){return B(unAppCStr("no parse on ",[1,_14j,_14X]));})]:(E(_14Z[2])[0]==0)?[1,_14Z[1]]:[0,new T(function(){return B(unAppCStr("ambiguous parse on ",[1,_14j,_14X]));})];},_150=function(_151,_){var _152=B(A(_W7,[_6R,new T(function(){return toJSStr(E(_151));},1),_])),_153=E(_152);if(!_153[0]){return _6J;}else{var _154=B(A(_106,[_S,_ni,_153[1],_14i,_])),_155=E(_154);return (_155[0]==0)?_6J:new T(function(){var _156=B(_14U(_14h,_155[1]));if(!_156[0]){return [0];}else{return [1,_156[1]];}});}},_157=new T(function(){return B(unCStr("bottom"));}),_158=new T(function(){return B(unCStr("offset"));}),_159=new T(function(){return B(unCStr("loadPath"));}),_15a=function(_){var _15b=function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);},_15c=E(_15b)("processDump",toJSStr(_159));return new F(function(){return _v6(_);});},_15d=function(_15e,_){return new F(function(){return _15a(_);});},_15f="stepSize",_15g=new T(function(){return B(_W7(_6R,_15f));}),_15h="loadPath",_15i=new T(function(){return B(_W7(_6R,_15h));}),_15j=function(_15k){return E(_15k)[2];},_15l=function(_){return _6J;},_15m=function(_15n,_){return new F(function(){return _15l(_);});},_15o=[0,_15j,_15m],_15p=function(_15q,_15r){while(1){var _15s=E(_15q);if(!_15s[0]){return E(_15r);}else{var _15t=_15s[2],_15u=E(_15s[1]);if(_15r>_15u){_15q=_15t;_15r=_15u;continue;}else{_15q=_15t;continue;}}}},_15v=function(_15w,_15x,_15y){var _15z=E(_15w);if(_15y>_15z){return new F(function(){return _15p(_15x,_15z);});}else{return new F(function(){return _15p(_15x,_15y);});}},_15A=2,_15B=4,_15C=3,_15D=function(_15E,_15F){var _15G=function(_15H,_15I){while(1){var _15J=B((function(_15K,_15L){var _15M=E(_15K);if(!_15M[0]){return [0];}else{var _15N=_15M[2];if(!B(A(_15E,[_15M[1]]))){var _15O=_15L+1|0;_15H=_15N;_15I=_15O;return null;}else{return [1,_15L,new T(function(){return B(_15G(_15N,_15L+1|0));})];}}})(_15H,_15I));if(_15J!=null){return _15J;}}},_15P=B(_15G(_15F,0));return (_15P[0]==0)?[0]:[1,_15P[1]];},_15Q=function(_15R){return E(_15R);},_15S=function(_15T,_15U,_15V,_){var _15W=function(_15X,_){var _15Y=E(_15T),_15Z=rMV(_15Y),_160=E(E(_15Z)[2]),_161=new T(function(){var _162=new T(function(){var _163=E(E(_15X)[1]);return [0,new T(function(){return B(_15Q(_163[1]));}),new T(function(){return B(_15Q(_163[2]));})];}),_164=new T(function(){var _165=E(_162),_166=E(_160[1]);return Math.pow(E(_165[1])-E(_166[1]),2)+Math.pow(E(_165[2])-E(_166[2]),2);}),_167=new T(function(){var _168=E(_162),_169=E(_160[2]);return Math.pow(E(_168[1])-E(_169[1]),2)+Math.pow(E(_168[2])-E(_169[2]),2);}),_16a=[1,new T(function(){var _16b=E(_162),_16c=E(_160[3]);return Math.pow(E(_16b[1])-E(_16c[1]),2)+Math.pow(E(_16b[2])-E(_16c[2]),2);}),[1,new T(function(){var _16d=E(_162),_16e=E(_160[4]);return Math.pow(E(_16d[1])-E(_16e[1]),2)+Math.pow(E(_16d[2])-E(_16e[2]),2);}),_1l]],_16f=new T(function(){return B(_15v(_167,_16a,E(_164)));}),_16g=B(_15D(function(_16h){return E(_16f)==E(_16h);},[1,_164,[1,_167,_16a]]));if(!_16g[0]){return 3;}else{switch(E(_16g[1])){case 0:return 0;break;case 1:return 2;break;case 3:return 1;break;default:return 3;}}}),_=wMV(_15Y,[0,[1,_161],_160]);return new F(function(){return A(_15V,[_]);});},_16i=B(A(_ss,[_6S,_15o,_pL,_15U,_15A,_15W,_])),_16j=B(A(_ss,[_6S,_15o,_pL,_15U,_15C,function(_16k,_){var _16l=E(_15T),_16m=rMV(_16l),_=wMV(_16l,[0,_1V,E(_16m)[2]]);return new F(function(){return A(_15V,[_]);});},_])),_16n=function(_16o,_){var _16p=E(_15T),_16q=rMV(_16p),_16r=E(_16q),_16s=_16r[2],_16t=E(_16r[1]);if(!_16t[0]){var _16u=E(_16r);}else{var _16v=new T(function(){var _16w=E(E(_16o)[1]);return [0,new T(function(){return B(_15Q(_16w[1]));}),new T(function(){return B(_15Q(_16w[2]));})];});switch(E(_16t[1])){case 0:var _16x=E(_16s),_16y=[0,_16t,[0,_16v,_16x[2],_16x[3],_16x[4]]];break;case 1:var _16z=E(_16s),_16y=[0,_16t,[0,_16z[1],_16z[2],_16z[3],_16v]];break;case 2:var _16A=E(_16s),_16y=[0,_16t,[0,_16A[1],_16v,_16A[3],_16A[4]]];break;default:var _16B=E(_16s),_16y=[0,_16t,[0,_16B[1],_16B[2],_16v,_16B[4]]];}var _16u=_16y;}var _=wMV(_16p,_16u);return new F(function(){return A(_15V,[_]);});},_16C=B(A(_ss,[_6S,_15o,_pL,_15U,_15B,_16n,_]));return _a;},_16D=function(_16E,_16F,_16G,_16H,_16I,_16J,_16K,_16L,_16M){if(!E(_16F)){return [0,_31,_16G,_16H,_16I,_16J,_16K,_16L,_16M];}else{var _16N=E(_16G);if(!_16N[0]){return [0,_2Z,_1l,_16H,_16I,_16J,_16K,_16L,_16M];}else{var _16O=new T(function(){return E(E(_16N[1])[1]);});return [0,_2Z,[1,[0,_16O,new T(function(){var _16P=E(_16O),_16Q=_16P[1],_16R=E(E(_16E)[1]),_16S=_16R[1],_16T=E(_16R[2]),_16U=E(_16P[2]),_16V=_16T-_16U;if(!_16V){var _16W=E(_16S),_16X=E(_16Q),_16Y=_16W-_16X;if(!_16Y){return [0,_16W,_16U];}else{if(_16Y<=0){if(0<= -_16Y){return [0,_16W,_16U];}else{return [0,_16X,_16T];}}else{if(0<=_16Y){return [0,_16W,_16U];}else{return [0,_16X,_16T];}}}}else{if(_16V<=0){var _16Z=E(_16S),_170=E(_16Q),_171=_16Z-_170;if(!_171){if( -_16V<=0){return [0,_16Z,_16U];}else{return [0,_170,_16T];}}else{if(_171<=0){if( -_16V<= -_171){return [0,_16Z,_16U];}else{return [0,_170,_16T];}}else{if( -_16V<=_171){return [0,_16Z,_16U];}else{return [0,_170,_16T];}}}}else{var _172=E(_16S),_173=E(_16Q),_174=_172-_173;if(!_174){return [0,_173,_16T];}else{if(_174<=0){if(_16V<= -_174){return [0,_172,_16U];}else{return [0,_173,_16T];}}else{if(_16V<=_174){return [0,_172,_16U];}else{return [0,_173,_16T];}}}}}}),_1l],_16N[2]],_16H,_16I,_16J,_16K,_16L,_16M];}}},_175=function(_176,_177,_178,_){var _179=function(_17a,_){var _17b=E(_176),_17c=rMV(_17b),_17d=E(_17c),_17e=new T(function(){var _17f=E(E(_17a)[1]);return [0,new T(function(){return B(_15Q(_17f[1]));}),new T(function(){return B(_15Q(_17f[2]));})];}),_=wMV(_17b,[0,_2Z,[1,[0,_17e,_17e,_1l],_17d[2]],_17d[3],_17d[4],_17d[5],_17d[6],_17d[7],_17d[8]]);return new F(function(){return A(_178,[_]);});},_17g=B(A(_ss,[_6S,_15o,_pL,_177,_15A,_179,_])),_17h=B(A(_ss,[_6S,_15o,_pL,_177,_15C,function(_17i,_){var _17j=E(_176),_17k=rMV(_17j),_17l=E(_17k),_17m=B(_16D(_17i,_17l[1],_17l[2],_17l[3],_17l[4],_17l[5],_17l[6],_17l[7],_17l[8])),_=wMV(_17j,[0,_31,_17m[2],_17m[3],_17m[4],_17m[5],_17m[6],_17m[7],_17m[8]]);return new F(function(){return A(_178,[_]);});},_])),_17n=B(A(_ss,[_6S,_15o,_pL,_177,_15B,function(_17o,_){var _17p=E(_176),_17q=rMV(_17p),_17r=E(_17q),_17s=B(_16D(_17o,_17r[1],_17r[2],_17r[3],_17r[4],_17r[5],_17r[6],_17r[7],_17r[8])),_=wMV(_17p,[0,_17s[1],_17s[2],_17s[3],_17s[4],_17s[5],_17s[6],_17s[7],_17s[8]]);return new F(function(){return A(_178,[_]);});},_]));return _a;},_17t=new T(function(){return document;}),_17u=function(_17v,_){var _17w=E(_17v);if(!_17w[0]){return _1l;}else{var _17x=B(_17u(_17w[2],_));return [1,_17w[1],_17x];}},_17y=function(_17z,_){var _17A=__arr2lst(0,_17z);return new F(function(){return _17u(_17A,_);});},_17B=(function(e,q){if(!e || typeof e.querySelectorAll !== 'function') {return [];} else {return e.querySelectorAll(q);}}),_17C=function(_17D,_17E,_17F){var _17G=function(_){var _17H=E(_17B)(E(_17E),toJSStr(E(_17F)));return new F(function(){return _17y(_17H,_);});};return new F(function(){return A(_2,[_17D,_17G]);});},_17I=(function(x){return document.getElementById(x).value;}),_17J=(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);}),_17K=0,_17L=[0,_17K,_17K],_17M=653,_17N=[0,_17M,_17K],_17O=986,_17P=[0,_17M,_17O],_17Q=[0,_17K,_17O],_17R=[0,_17L,_17Q,_17P,_17N],_17S=[0,_1V,_17R],_17T=50,_17U=5,_17V=0,_17W=function(_17X,_17Y,_17Z){var _180=E(_17Y),_181=E(_17Z),_182=new T(function(){var _183=B(_Kl(_17X)),_184=B(_17W(_17X,_181,B(A(_Ij,[_183,new T(function(){return B(A(_Ji,[_183,_181,_181]));}),_180]))));return [1,_184[1],_184[2]];});return [0,_180,_182];},_185=function(_186){return E(E(_186)[2]);},_187=function(_188){return E(E(_188)[4]);},_189=function(_18a){return E(E(_18a)[6]);},_18b=function(_18c,_18d){var _18e=E(_18d);if(!_18e[0]){return [0];}else{var _18f=_18e[1];return (!B(A(_18c,[_18f])))?[0]:[1,_18f,new T(function(){return B(_18b(_18c,_18e[2]));})];}},_18g=function(_18h,_18i,_18j,_18k,_18l){var _18m=B(_17W(_18i,_18j,_18k)),_18n=new T(function(){var _18o=new T(function(){return B(_Kl(_18i));}),_18p=new T(function(){return B(A(_185,[_18i,new T(function(){return B(A(_Ij,[_18o,_18k,_18j]));}),new T(function(){return B(A(_Ip,[_18o,_Io]));})]));});if(!B(A(_189,[_18h,_18k,_18j]))){var _18q=new T(function(){return B(A(_Ji,[_18o,_18l,_18p]));});return function(_18r){return new F(function(){return A(_189,[_18h,_18r,_18q]);});};}else{var _18s=new T(function(){return B(A(_Ji,[_18o,_18l,_18p]));});return function(_18t){return new F(function(){return A(_187,[_18h,_18t,_18s]);});};}});return new F(function(){return _18b(_18n,[1,_18m[1],_18m[2]]);});},_18u=new T(function(){return B(_18g(_En,_C8,_17V,_17U,_17T));}),_18v=function(_18w){return E(_18w)*1.7453292519943295e-2;},_18x=new T(function(){return B(_bc(_18v,_18u));}),_18y=0.5,_18z=[0,_31,_1l,_17V,_17T,_17V,_2R,_18y,_18x],_18A=[1,_a],_18B=new T(function(){return B(unCStr("Page Missing element expected by Main"));}),_18C=new T(function(){return B(_Wq(_18B,_Wo));}),_18D=[1,_Wn,_18C],_18E=new T(function(){return B(unCStr("Could not read offset elements"));}),_18F=new T(function(){return B(_Wq(_18E,_Wo));}),_18G=[1,_Wn,_18F],_18H=new T(function(){return B(unCStr("input[name=\'mount\']:checked"));}),_18I=new T(function(){return B(unCStr("top"));}),_18J=new T(function(){return B(unCStr("Could not load element step size"));}),_18K=new T(function(){return B(_Wq(_18J,_Wo));}),_18L=[1,_Wn,_18K],_18M=new T(function(){return B(unCStr("stepSize"));}),_18N=new T(function(){return B(unCStr("Could not read rotations"));}),_18O=new T(function(){return B(_Wq(_18N,_Wo));}),_18P=[1,_Wn,_18O],_18Q=function(_18R,_18S){var _18T=B(_14U(_14h,_18R));if(!_18T[0]){return [0];}else{var _18U=E(_18S);return (_18U[0]==0)?[0]:[1,[1,_18T[1],_18U[1]]];}},_18V=[1,_1l],_18W="rotations",_18X=new T(function(){return B(unCStr("download"));}),_18Y=new T(function(){return B(unCStr(".txt"));}),_18Z=new T(function(){return B(unCStr(".json"));}),_190=new T(function(){return B(unCStr("filePath"));}),_191="filePath",_192=new T(function(){return B(unCStr("failed to decode JSON"));}),_193=[1,_Wn,_1l],_194=new T(function(){return B(_Wq(_192,_193));}),_195=[1,_Wn,_194],_196=new T(function(){return B(unCStr("input[name=\'mount\']"));}),_197=new T(function(){return B(unCStr("IndianRoller2.jpg"));}),_198=function(_199){return E(_199)*1.7453292519943295e-2;},_19a=function(_19b,_19c){var _19d=E(_19c);if(!_19d[0]){return [0,_1l,_1l];}else{var _19e=_19d[1];if(!B(A(_19b,[_19e]))){var _19f=new T(function(){var _19g=B(_19a(_19b,_19d[2]));return [0,_19g[1],_19g[2]];});return [0,[1,_19e,new T(function(){return E(E(_19f)[1]);})],new T(function(){return E(E(_19f)[2]);})];}else{return [0,_1l,_19d];}}},_19h=function(_19i){var _19j=_19i>>>0;if(_19j>887){var _19k=u_iswspace(_19i);return (E(_19k)==0)?false:true;}else{var _19l=E(_19j);return (_19l==32)?true:(_19l-9>>>0>4)?(E(_19l)==160)?true:false:true;}},_19m=function(_19n){return new F(function(){return _19h(E(_19n));});},_19o=function(_19p,_19q,_19r){var _19s=function(_19t){var _19u=B(_13y(_19m,_19t));if(!_19u[0]){return E(_19q);}else{var _19v=new T(function(){var _19w=B(_19a(_19m,_19u));return [0,_19w[1],_19w[2]];});return new F(function(){return A(_19p,[new T(function(){return E(E(_19v)[1]);}),new T(function(){return B(_19s(E(_19v)[2]));})]);});}};return new F(function(){return _19s(_19r);});},_19x=function(_){var _19y=nMV(_17S),_19z=_19y,_19A=nMV(_18z),_19B=_19A,_19C=B(A(_5,[_6R,_197,_])),_19D=nMV(_19C),_19E=_19D,_19F=nMV(_197),_19G=_19F,_19H=B(A(_17C,[_6R,_17t,_196,_])),_19I=_19H,_19J=function(_19K,_){var _19L=String(E(_19K)),_19M=jsParseJSON(_19L);if(!_19M[0]){var _19N=B(_Wi(_Wx,_195,_));return _pk;}else{var _19O=B(_4u(_19M[1]));if(!_19O[0]){var _19P=B(_Wi(_Wx,_195,_));return _pk;}else{var _19Q=_19O[1],_=wMV(_19z,new T(function(){return E(E(_19Q)[1]);})),_=wMV(_19B,new T(function(){return E(E(_19Q)[2]);}));return _pk;}}},_19R=__createJSFunc(2,E(_19J)),_19S=(function(s,f){Haste[s] = f;}),_19T=E(_19S)("processDump",_19R),_19U=B(A(_W7,[_6R,_191,_])),_19V=E(_19U);if(!_19V[0]){var _19W=B(_Wi(_Wx,_18D,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _19X=B(A(_15i,[_])),_19Y=E(_19X);if(!_19Y[0]){var _19Z=B(_Wi(_Wx,_18D,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1a0=function(_1a1,_){var _1a2=E(_1a1),_1a3=toJSStr(_190),_1a4=E(_17J)(_1a3),_1a5=B(A(_5,[_6R,new T(function(){var _1a6=String(_1a4);return fromJSStr(_1a6);}),_])),_=wMV(_19E,_1a5),_1a7=E(_17I)(_1a3),_1a8=new T(function(){var _1a9=String(_1a7);return fromJSStr(_1a9);}),_=wMV(_19G,_1a8),_1aa=B(_Wy(_Zr,_18X,new T(function(){return B(_16(_1a8,_18Z));},1),_)),_1ab=B(_Wy(_Zs,_18X,new T(function(){return B(_16(_1a8,_18Y));},1),_));return new F(function(){return _10C(_19B,_19z,_19E,_);});},_1ac=B(A(_ss,[_6S,_S,_o,_19V[1],_rw,_1a0,_])),_1ad=B(A(_ss,[_6S,_S,_o,_19Y[1],_rw,_15d,_])),_1ae=B(A(_W7,[_6R,_18W,_])),_1af=E(_1ae);if(!_1af[0]){var _1ag=B(_Wi(_Wx,_18D,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1ah=_1af[1],_1ai=B(A(_15g,[_])),_1aj=E(_1ai);if(!_1aj[0]){var _1ak=B(_Wi(_Wx,_18D,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1al=_1aj[1],_1am=B(A(_W7,[_6R,_ZA,_])),_1an=E(_1am);if(!_1an[0]){var _1ao=B(_Wi(_Wx,_18D,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1ap=E(_1an[1]),_1aq=E(_N),_1ar=_1aq(_1ap);if(!_1ar){var _1as=B(_Wi(_Wx,_18D,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1at=E(_M),_1au=_1at(_1ap),_1av=_1au,_1aw=B(A(_W7,[_6R,_Zv,_])),_1ax=function(_,_1ay){var _1az=E(_1ay);if(!_1az[0]){var _1aA=B(_Wi(_Wx,_18D,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1aB=function(_){return new F(function(){return _10C(_19B,_19z,_19E,_);});},_1aC=B(_15S(_19z,[0,_1av,_1ap],_1aB,_)),_1aD=B(_175(_19B,_1az[1],_1aB,_)),_1aE=B(A(_11K,[_])),_1aF=E(_1aE);if(!_1aF[0]){var _1aG=B(_Wi(_Wx,_18D,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1aH=_1aF[1],_1aI=B(A(_11I,[_])),_1aJ=E(_1aI);if(!_1aJ[0]){var _1aK=B(_Wi(_Wx,_18D,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1aL=_1aJ[1],_1aM=B(A(_11G,[_])),_1aN=E(_1aM);if(!_1aN[0]){var _1aO=B(_Wi(_Wx,_18D,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1aP=_1aN[1],_1aQ=function(_){var _1aR=B(A(_W7,[_6R,_18W,_])),_1aS=function(_){var _1aT=B(_Wi(_Wx,_18P,_)),_1aU=B(_150(_18M,_)),_1aV=function(_,_1aW){var _1aX=function(_){var _1aY=B(_150(_18I,_)),_1aZ=E(_1aY);if(!_1aZ[0]){var _1b0=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1b1=B(_150(_157,_)),_1b2=E(_1b1);if(!_1b2[0]){var _1b3=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1b4=B(_150(_158,_)),_1b5=E(_1b4);if(!_1b5[0]){var _1b6=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1b7=B(A(_17C,[_ni,_17t,_18H,_])),_1b8=function(_,_1b9){var _1ba=E(_1b9);if(!_1ba[0]){var _1bb=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1bc=B(A(_106,[_S,_ni,_1ba[1],_14i,_])),_1bd=E(_1bc);if(!_1bd[0]){var _1be=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1bf=B(_14U(_lA,_1bd[1]));if(!_1bf[0]){var _1bg=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1bh=rMV(_19B),_1bi=E(_1bh),_=wMV(_19B,[0,_1bi[1],_1bi[2],_1aZ[1],_1b2[1],_1b5[1],_1bf[1],_1bi[7],_1bi[8]]);return new F(function(){return _10C(_19B,_19z,_19E,_);});}}}},_1bj=E(_1b7);if(!_1bj[0]){return new F(function(){return _1b8(_,_6J);});}else{var _1bk=E(_1bj[1]);if(!_1bk[0]){return new F(function(){return _1b8(_,_6J);});}else{return new F(function(){return _1b8(_,[1,_1bk[1]]);});}}}}}};if(!E(_1aW)[0]){var _1bl=B(_Wi(_Wx,_18L,_));return new F(function(){return _1aX(_);});}else{return new F(function(){return _1aX(_);});}},_1bm=E(_1aU);if(!_1bm[0]){return new F(function(){return _1aV(_,_6J);});}else{var _1bn=rMV(_19B),_1bo=E(_1bn),_=wMV(_19B,[0,_1bo[1],_1bo[2],_1bo[3],_1bo[4],_1bo[5],_1bo[6],_1bm[1],_1bo[8]]);return new F(function(){return _1aV(_,_18A);});}},_1bp=E(_1aR);if(!_1bp[0]){return new F(function(){return _1aS(_);});}else{var _1bq=B(A(_106,[_S,_ni,_1bp[1],_14i,_])),_1br=E(_1bq);if(!_1br[0]){return new F(function(){return _1aS(_);});}else{var _1bs=B(_14U(_md,_1br[1]));if(!_1bs[0]){return new F(function(){return _1aS(_);});}else{var _1bt=function(_,_1bu){var _1bv=function(_){var _1bw=B(_150(_18M,_)),_1bx=function(_,_1by){var _1bz=function(_){var _1bA=B(_150(_18I,_)),_1bB=E(_1bA);if(!_1bB[0]){var _1bC=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1bD=B(_150(_157,_)),_1bE=E(_1bD);if(!_1bE[0]){var _1bF=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1bG=B(_150(_158,_)),_1bH=E(_1bG);if(!_1bH[0]){var _1bI=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1bJ=B(A(_17C,[_ni,_17t,_18H,_])),_1bK=function(_,_1bL){var _1bM=E(_1bL);if(!_1bM[0]){var _1bN=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1bO=B(A(_106,[_S,_ni,_1bM[1],_14i,_])),_1bP=E(_1bO);if(!_1bP[0]){var _1bQ=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1bR=B(_14U(_lA,_1bP[1]));if(!_1bR[0]){var _1bS=B(_Wi(_Wx,_18G,_));return new F(function(){return _10C(_19B,_19z,_19E,_);});}else{var _1bT=rMV(_19B),_1bU=E(_1bT),_=wMV(_19B,[0,_1bU[1],_1bU[2],_1bB[1],_1bE[1],_1bH[1],_1bR[1],_1bU[7],_1bU[8]]);return new F(function(){return _10C(_19B,_19z,_19E,_);});}}}},_1bV=E(_1bJ);if(!_1bV[0]){return new F(function(){return _1bK(_,_6J);});}else{var _1bW=E(_1bV[1]);if(!_1bW[0]){return new F(function(){return _1bK(_,_6J);});}else{return new F(function(){return _1bK(_,[1,_1bW[1]]);});}}}}}};if(!E(_1by)[0]){var _1bX=B(_Wi(_Wx,_18L,_));return new F(function(){return _1bz(_);});}else{return new F(function(){return _1bz(_);});}},_1bY=E(_1bw);if(!_1bY[0]){return new F(function(){return _1bx(_,_6J);});}else{var _1bZ=rMV(_19B),_1c0=E(_1bZ),_=wMV(_19B,[0,_1c0[1],_1c0[2],_1c0[3],_1c0[4],_1c0[5],_1c0[6],_1bY[1],_1c0[8]]);return new F(function(){return _1bx(_,_18A);});}};if(!E(_1bu)[0]){var _1c1=B(_Wi(_Wx,_18P,_));return new F(function(){return _1bv(_);});}else{return new F(function(){return _1bv(_);});}},_1c2=B(_19o(_18Q,_18V,_1bs[1]));if(!_1c2[0]){return new F(function(){return _1bt(_,_6J);});}else{var _1c3=rMV(_19B),_1c4=E(_1c3),_=wMV(_19B,[0,_1c4[1],_1c4[2],_1c4[3],_1c4[4],_1c4[5],_1c4[6],_1c4[7],new T(function(){return B(_bc(_198,_1c2[1]));})]);return new F(function(){return _1bt(_,_18A);});}}}}},_1c5=function(_1c6,_){return new F(function(){return _1aQ(_);});},_1c7=function(_1c8,_){while(1){var _1c9=E(_1c8);if(!_1c9[0]){var _1ca=B(A(_ss,[_6S,_S,_o,_1al,_rw,_1c5,_])),_1cb=B(A(_ss,[_6S,_S,_o,_1ah,_rw,_1c5,_])),_1cc=B(A(_ss,[_6S,_S,_o,_1aH,_rw,_1c5,_])),_1cd=B(A(_ss,[_6S,_S,_o,_1aL,_rw,_1c5,_])),_1ce=B(A(_ss,[_6S,_S,_o,_1aP,_rw,_1c5,_]));return _a;}else{var _1cf=B(A(_ss,[_6S,_S,_o,_1c9[1],_rw,_1c5,_]));_1c8=_1c9[2];continue;}}},_1cg=B(_1c7(_19I,_)),_1ch=B(A(_ss,[_6S,_S,_L,_1al,_11E,_1c5,_])),_1ci=B(A(_ss,[_6S,_S,_L,_1ah,_11E,_1c5,_])),_1cj=B(A(_ss,[_6S,_S,_L,_1aH,_11E,_1c5,_])),_1ck=B(A(_ss,[_6S,_S,_L,_1aL,_11E,_1c5,_])),_1cl=B(A(_ss,[_6S,_S,_L,_1aP,_11E,_1c5,_]));return new F(function(){return _10C(_19B,_19z,_19E,_);});}}}}},_1cm=E(_1aw);if(!_1cm[0]){return new F(function(){return _1ax(_,_6J);});}else{var _1cn=E(_1cm[1]),_1co=_1aq(_1cn);if(!_1co){return new F(function(){return _1ax(_,_6J);});}else{var _1cp=_1at(_1cn);return new F(function(){return _1ax(_,[1,[0,_1cp,_1cn]]);});}}}}}}}}},_1cq=function(_){return new F(function(){return _19x(_);});};
var hasteMain = function() {B(A(_1cq, [0]));};window.onload = hasteMain;