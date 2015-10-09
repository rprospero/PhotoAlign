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

var _0="src",_1=(function(e,p,v){e[p] = v;}),_2=function(_3){return E(E(_3)[2]);},_4=(function(t){return document.createElement(t);}),_5=function(_6,_7){return new F(function(){return A(_2,[_6,function(_){var _8=E(_4)("img"),_9=E(_1)(_8,E(_0),toJSStr(E(_7)));return _8;}]);});},_a=0,_b=function(_){return _a;},_c=function(_d,_e,_){return new F(function(){return _b(_);});},_f="scroll",_g="submit",_h="blur",_i="focus",_j="change",_k="unload",_l="load",_m=function(_n){switch(E(_n)){case 0:return E(_l);case 1:return E(_k);case 2:return E(_j);case 3:return E(_i);case 4:return E(_h);case 5:return E(_g);default:return E(_f);}},_o=[0,_m,_c],_p="metaKey",_q="shiftKey",_r="altKey",_s="ctrlKey",_t="keyCode",_u=function(_v,_){var _w=_v[E(_t)],_x=_v[E(_s)],_y=_v[E(_r)],_z=_v[E(_q)],_A=_v[E(_p)];return new T(function(){var _B=Number(_w),_C=jsTrunc(_B);return [0,_C,E(_x),E(_y),E(_z),E(_A)];});},_D=function(_E,_F,_){return new F(function(){return _u(E(_F),_);});},_G="keydown",_H="keyup",_I="keypress",_J=function(_K){switch(E(_K)){case 0:return E(_I);case 1:return E(_H);default:return E(_G);}},_L=[0,_J,_D],_M=(function(e){return e.getContext('2d');}),_N=(function(e){return !!e.getContext;}),_O=function(_P,_){return [1,_P];},_Q=function(_R){return E(_R);},_S=[0,_Q,_O],_T=function(_U){return E(E(_U)[1]);},_V=function(_W,_X){return (!B(A(_T,[_Y,_W,_X])))?true:false;},_Z=function(_10,_11){var _12=strEq(E(_10),E(_11));return (E(_12)==0)?false:true;},_13=function(_14,_15){return new F(function(){return _Z(_14,_15);});},_Y=new T(function(){return [0,_13,_V];}),_16=function(_17,_18){var _19=E(_17);return (_19[0]==0)?E(_18):[1,_19[1],new T(function(){return B(_16(_19[2],_18));})];},_1a=new T(function(){return B(unCStr("!!: negative index"));}),_1b=new T(function(){return B(unCStr("Prelude."));}),_1c=new T(function(){return B(_16(_1b,_1a));}),_1d=new T(function(){return B(err(_1c));}),_1e=new T(function(){return B(unCStr("!!: index too large"));}),_1f=new T(function(){return B(_16(_1b,_1e));}),_1g=new T(function(){return B(err(_1f));}),_1h=function(_1i,_1j){while(1){var _1k=E(_1i);if(!_1k[0]){return E(_1g);}else{var _1l=E(_1j);if(!_1l){return E(_1k[1]);}else{_1i=_1k[2];_1j=_1l-1|0;continue;}}}},_1m=function(_1n,_1o){if(_1o>=0){return new F(function(){return _1h(_1n,_1o);});}else{return E(_1d);}},_1p=new T(function(){return B(unCStr(": empty list"));}),_1q=function(_1r){return new F(function(){return err(B(_16(_1b,new T(function(){return B(_16(_1r,_1p));},1))));});},_1s=new T(function(){return B(unCStr("head"));}),_1t=new T(function(){return B(_1q(_1s));}),_1u=function(_1v){var _1w=E(_1v);if(_1w[0]==3){var _1x=E(_1w[1]);if(!_1x[0]){return E(_1t);}else{var _1y=E(_1x[1]);if(!_1y[0]){var _1z=B(_1m(_1x,1));return (_1z[0]==0)?[1,[0,_1y[1],_1z[1]]]:[0];}else{return [0];}}}else{return [0];}},_1A=function(_1B,_1C){var _1D=E(_1C);return (_1D[0]==0)?[0]:[1,new T(function(){return B(A(_1B,[_1D[1]]));}),new T(function(){return B(_1A(_1B,_1D[2]));})];},_1E=function(_1F){var _1G=E(_1F);if(_1G[0]==3){var _1H=B(_1A(_1u,_1G[1]));if(!_1H[0]){return E(_1t);}else{var _1I=E(_1H[1]);if(!_1I[0]){return [0];}else{var _1J=B(_1m(_1H,1));if(!_1J[0]){return [0];}else{var _1K=B(_1m(_1H,2));if(!_1K[0]){return [0];}else{var _1L=B(_1m(_1H,3));return (_1L[0]==0)?[0]:[1,[0,_1I[1],_1J[1],_1K[1],_1L[1]]];}}}}}else{return [0];}},_1M="box",_1N="mouse",_1O="corner",_1P="Dragging",_1Q=[0],_1R=[1,_1Q],_1S="Free",_1T="state",_1U=1,_1V=[1,_1U],_1W=0,_1X=[1,_1W],_1Y=3,_1Z=[1,_1Y],_20=2,_21=[1,_20],_22=new T(function(){return B(unCStr("SW"));}),_23=new T(function(){return B(unCStr("SE"));}),_24=new T(function(){return B(unCStr("NW"));}),_25=new T(function(){return B(unCStr("NE"));}),_26=function(_27,_28){while(1){var _29=E(_27);if(!_29[0]){return (E(_28)[0]==0)?true:false;}else{var _2a=E(_28);if(!_2a[0]){return false;}else{if(E(_29[1])!=E(_2a[1])){return false;}else{_27=_29[2];_28=_2a[2];continue;}}}}},_2b=function(_2c){var _2d=E(_2c);if(_2d[0]==1){var _2e=fromJSStr(_2d[1]);return (!B(_26(_2e,_25)))?(!B(_26(_2e,_24)))?(!B(_26(_2e,_23)))?(!B(_26(_2e,_22)))?[0]:E(_21):E(_1Z):E(_1X):E(_1V);}else{return [0];}},_2f=function(_2g,_2h,_2i){while(1){var _2j=E(_2i);if(!_2j[0]){return [0];}else{var _2k=E(_2j[1]);if(!B(A(_T,[_2g,_2h,_2k[1]]))){_2i=_2j[2];continue;}else{return [1,_2k[2]];}}}},_2l=function(_2m){var _2n=E(_2m);if(_2n[0]==4){var _2o=_2n[1],_2p=B(_2f(_Y,_1T,_2o));if(!_2p[0]){return [0];}else{var _2q=E(_2p[1]);if(_2q[0]==1){var _2r=_2q[1],_2s=strEq(_2r,E(_1S));if(!E(_2s)){var _2t=strEq(_2r,E(_1P));if(!E(_2t)){return [0];}else{var _2u=B(_2f(_Y,_1O,_2o));if(!_2u[0]){return [0];}else{var _2v=B(_2b(_2u[1]));return (_2v[0]==0)?[0]:[1,[1,_2v[1]]];}}}else{return E(_1R);}}else{return [0];}}}else{return [0];}},_2w=function(_2x){var _2y=E(_2x);if(_2y[0]==4){var _2z=_2y[1],_2A=B(_2f(_Y,_1N,_2z));if(!_2A[0]){return [0];}else{var _2B=B(_2l(_2A[1]));if(!_2B[0]){return [0];}else{var _2C=B(_2f(_Y,_1M,_2z));if(!_2C[0]){return [0];}else{var _2D=B(_1E(_2C[1]));return (_2D[0]==0)?[0]:[1,[0,_2B[1],_2D[1]]];}}}}else{return [0];}},_2E=function(_2F){return [0,E(_2F)];},_2G=function(_2H){var _2I=E(_2H);return (_2I[0]==0)?[1,_2I[1]]:[0];},_2J=[0,_2E,_2G],_2K=1,_2L=[1,_2K],_2M=0,_2N=[1,_2M],_2O=new T(function(){return B(unCStr("Top"));}),_2P=new T(function(){return B(unCStr("Bottom"));}),_2Q=function(_2R){var _2S=E(_2R);if(_2S[0]==1){var _2T=fromJSStr(_2S[1]);return (!B(_26(_2T,_2P)))?(!B(_26(_2T,_2O)))?[0]:E(_2N):E(_2L);}else{return [0];}},_2U=1,_2V=[1,_2U],_2W=0,_2X=[1,_2W],_2Y=new T(function(){return B(unCStr("Free"));}),_2Z=new T(function(){return B(unCStr("Dragging"));}),_30=function(_31){var _32=E(_31);if(_32[0]==1){var _33=fromJSStr(_32[1]);return (!B(_26(_33,_2Z)))?(!B(_26(_33,_2Y)))?[0]:E(_2X):E(_2V);}else{return [0];}},_34="title",_35="points",_36=function(_37){var _38=E(_37);if(_38[0]==4){var _39=_38[1],_3a=B(_2f(_Y,_35,_39));if(!_3a[0]){return [0];}else{var _3b=E(_3a[1]);if(_3b[0]==3){var _3c=E(_3b[1]);if(!_3c[0]){return E(_1t);}else{var _3d=E(_3c[1]);if(_3d[0]==3){var _3e=E(_3d[1]);if(!_3e[0]){return E(_1t);}else{var _3f=E(_3e[1]);if(!_3f[0]){var _3g=B(_1m(_3e,1));if(!_3g[0]){var _3h=B(_1m(_3c,1));if(_3h[0]==3){var _3i=E(_3h[1]);if(!_3i[0]){return E(_1t);}else{var _3j=E(_3i[1]);if(!_3j[0]){var _3k=B(_1m(_3i,1));if(!_3k[0]){var _3l=B(_2f(_Y,_34,_39));if(!_3l[0]){return [0];}else{var _3m=E(_3l[1]);return (_3m[0]==1)?[1,[0,[0,_3f[1],_3g[1]],[0,_3j[1],_3k[1]],new T(function(){return fromJSStr(_3m[1]);})]]:[0];}}else{return [0];}}else{return [0];}}}else{return [0];}}else{return [0];}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}},_3n=[0],_3o=function(_3p){var _3q=new T(function(){var _3r=E(E(_3p)[2]);return [3,[1,new T(function(){return B(_2E(_3r[1]));}),[1,new T(function(){return B(_2E(_3r[2]));}),_3n]]];}),_3s=new T(function(){var _3t=E(E(_3p)[1]);return [3,[1,new T(function(){return B(_2E(_3t[1]));}),[1,new T(function(){return B(_2E(_3t[2]));}),_3n]]];});return [1,[0,_34,new T(function(){return [1,toJSStr(E(E(_3p)[3]))];})],[1,[0,_35,[3,[1,_3s,[1,_3q,_3n]]]],_3n]];},_3u=function(_3v){return [4,E(B(_3o(_3v)))];},_3w=[0,_3u,_36],_3x="rotations",_3y="choice",_3z="offset",_3A="bottom",_3B="top",_3C="fileName",_3D="scans",_3E="mouse",_3F=[1,_3n],_3G=function(_3H){return E(E(_3H)[2]);},_3I=function(_3J,_3K){var _3L=E(_3K);if(_3L[0]==3){var _3M=new T(function(){return B(_3G(_3J));}),_3N=function(_3O){var _3P=E(_3O);if(!_3P[0]){return E(_3F);}else{var _3Q=B(A(_3M,[_3P[1]]));if(!_3Q[0]){return [0];}else{var _3R=B(_3N(_3P[2]));return (_3R[0]==0)?[0]:[1,[1,_3Q[1],_3R[1]]];}}};return new F(function(){return _3N(_3L[1]);});}else{return [0];}},_3S=function(_3T){var _3U=E(_3T);if(_3U[0]==4){var _3V=_3U[1],_3W=B(_2f(_Y,_3E,_3V));if(!_3W[0]){return [0];}else{var _3X=B(_30(_3W[1]));if(!_3X[0]){return [0];}else{var _3Y=B(_2f(_Y,_3D,_3V));if(!_3Y[0]){return [0];}else{var _3Z=B(_3I(_3w,_3Y[1]));if(!_3Z[0]){return [0];}else{var _40=B(_2f(_Y,_3C,_3V));if(!_40[0]){return [0];}else{var _41=E(_40[1]);if(_41[0]==1){var _42=B(_2f(_Y,_3B,_3V));if(!_42[0]){return [0];}else{var _43=E(_42[1]);if(!_43[0]){var _44=B(_2f(_Y,_3A,_3V));if(!_44[0]){return [0];}else{var _45=E(_44[1]);if(!_45[0]){var _46=B(_2f(_Y,_3z,_3V));if(!_46[0]){return [0];}else{var _47=E(_46[1]);if(!_47[0]){var _48=B(_2f(_Y,_3y,_3V));if(!_48[0]){return [0];}else{var _49=B(_2Q(_48[1]));if(!_49[0]){return [0];}else{var _4a=B(_2f(_Y,_3x,_3V));if(!_4a[0]){return [0];}else{var _4b=B(_3I(_2J,_4a[1]));return (_4b[0]==0)?[0]:[1,[0,_3X[1],_3Z[1],new T(function(){return fromJSStr(_41[1]);}),_43[1],_45[1],_47[1],_49[1],_4b[1]]];}}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}}}}}else{return [0];}},_4c="scans",_4d="calib",_4e=function(_4f){var _4g=E(_4f);if(_4g[0]==4){var _4h=_4g[1],_4i=B(_2f(_Y,_4d,_4h));if(!_4i[0]){return [0];}else{var _4j=B(_2w(_4i[1]));if(!_4j[0]){return [0];}else{var _4k=B(_2f(_Y,_4c,_4h));if(!_4k[0]){return [0];}else{var _4l=B(_3S(_4k[1]));return (_4l[0]==0)?[0]:[1,[0,_4j[1],_4l[1]]];}}}}else{return [0];}},_4m=function(_4n,_4o,_){var _4p=B(A(_4n,[_])),_4q=B(A(_4o,[_]));return _4p;},_4r=function(_4s,_4t,_){var _4u=B(A(_4s,[_])),_4v=B(A(_4t,[_]));return new T(function(){return B(A(_4u,[_4v]));});},_4w=function(_4x,_4y,_){var _4z=B(A(_4y,[_]));return _4x;},_4A=function(_4B,_4C,_){var _4D=B(A(_4C,[_]));return new T(function(){return B(A(_4B,[_4D]));});},_4E=[0,_4A,_4w],_4F=function(_4G,_){return _4G;},_4H=function(_4I,_4J,_){var _4K=B(A(_4I,[_]));return new F(function(){return A(_4J,[_]);});},_4L=[0,_4E,_4F,_4r,_4H,_4m],_4M=function(_4N,_4O,_){var _4P=B(A(_4N,[_]));return new F(function(){return A(_4O,[_4P,_]);});},_4Q=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_4R=new T(function(){return B(unCStr("base"));}),_4S=new T(function(){return B(unCStr("IOException"));}),_4T=new T(function(){var _4U=hs_wordToWord64(4053623282),_4V=hs_wordToWord64(3693590983);return [0,_4U,_4V,[0,_4U,_4V,_4R,_4Q,_4S],_3n,_3n];}),_4W=function(_4X){return E(_4T);},_4Y=function(_4Z){return E(E(_4Z)[1]);},_50=function(_51,_52,_53){var _54=B(A(_51,[_])),_55=B(A(_52,[_])),_56=hs_eqWord64(_54[1],_55[1]);if(!_56){return [0];}else{var _57=hs_eqWord64(_54[2],_55[2]);return (!_57)?[0]:[1,_53];}},_58=function(_59){var _5a=E(_59);return new F(function(){return _50(B(_4Y(_5a[1])),_4W,_5a[2]);});},_5b=new T(function(){return B(unCStr(": "));}),_5c=new T(function(){return B(unCStr(")"));}),_5d=new T(function(){return B(unCStr(" ("));}),_5e=new T(function(){return B(unCStr("interrupted"));}),_5f=new T(function(){return B(unCStr("system error"));}),_5g=new T(function(){return B(unCStr("unsatisified constraints"));}),_5h=new T(function(){return B(unCStr("user error"));}),_5i=new T(function(){return B(unCStr("permission denied"));}),_5j=new T(function(){return B(unCStr("illegal operation"));}),_5k=new T(function(){return B(unCStr("end of file"));}),_5l=new T(function(){return B(unCStr("resource exhausted"));}),_5m=new T(function(){return B(unCStr("resource busy"));}),_5n=new T(function(){return B(unCStr("does not exist"));}),_5o=new T(function(){return B(unCStr("already exists"));}),_5p=new T(function(){return B(unCStr("resource vanished"));}),_5q=new T(function(){return B(unCStr("timeout"));}),_5r=new T(function(){return B(unCStr("unsupported operation"));}),_5s=new T(function(){return B(unCStr("hardware fault"));}),_5t=new T(function(){return B(unCStr("inappropriate type"));}),_5u=new T(function(){return B(unCStr("invalid argument"));}),_5v=new T(function(){return B(unCStr("failed"));}),_5w=new T(function(){return B(unCStr("protocol error"));}),_5x=function(_5y,_5z){switch(E(_5y)){case 0:return new F(function(){return _16(_5o,_5z);});break;case 1:return new F(function(){return _16(_5n,_5z);});break;case 2:return new F(function(){return _16(_5m,_5z);});break;case 3:return new F(function(){return _16(_5l,_5z);});break;case 4:return new F(function(){return _16(_5k,_5z);});break;case 5:return new F(function(){return _16(_5j,_5z);});break;case 6:return new F(function(){return _16(_5i,_5z);});break;case 7:return new F(function(){return _16(_5h,_5z);});break;case 8:return new F(function(){return _16(_5g,_5z);});break;case 9:return new F(function(){return _16(_5f,_5z);});break;case 10:return new F(function(){return _16(_5w,_5z);});break;case 11:return new F(function(){return _16(_5v,_5z);});break;case 12:return new F(function(){return _16(_5u,_5z);});break;case 13:return new F(function(){return _16(_5t,_5z);});break;case 14:return new F(function(){return _16(_5s,_5z);});break;case 15:return new F(function(){return _16(_5r,_5z);});break;case 16:return new F(function(){return _16(_5q,_5z);});break;case 17:return new F(function(){return _16(_5p,_5z);});break;default:return new F(function(){return _16(_5e,_5z);});}},_5A=new T(function(){return B(unCStr("}"));}),_5B=new T(function(){return B(unCStr("{handle: "));}),_5C=function(_5D,_5E,_5F,_5G,_5H,_5I){var _5J=new T(function(){var _5K=new T(function(){var _5L=new T(function(){var _5M=E(_5G);if(!_5M[0]){return E(_5I);}else{var _5N=new T(function(){return B(_16(_5M,new T(function(){return B(_16(_5c,_5I));},1)));},1);return B(_16(_5d,_5N));}},1);return B(_5x(_5E,_5L));}),_5O=E(_5F);if(!_5O[0]){return E(_5K);}else{return B(_16(_5O,new T(function(){return B(_16(_5b,_5K));},1)));}}),_5P=E(_5H);if(!_5P[0]){var _5Q=E(_5D);if(!_5Q[0]){return E(_5J);}else{var _5R=E(_5Q[1]);if(!_5R[0]){var _5S=new T(function(){var _5T=new T(function(){return B(_16(_5A,new T(function(){return B(_16(_5b,_5J));},1)));},1);return B(_16(_5R[1],_5T));},1);return new F(function(){return _16(_5B,_5S);});}else{var _5U=new T(function(){var _5V=new T(function(){return B(_16(_5A,new T(function(){return B(_16(_5b,_5J));},1)));},1);return B(_16(_5R[1],_5V));},1);return new F(function(){return _16(_5B,_5U);});}}}else{return new F(function(){return _16(_5P[1],new T(function(){return B(_16(_5b,_5J));},1));});}},_5W=function(_5X){var _5Y=E(_5X);return new F(function(){return _5C(_5Y[1],_5Y[2],_5Y[3],_5Y[4],_5Y[6],_3n);});},_5Z=function(_60,_61,_62){var _63=E(_61);return new F(function(){return _5C(_63[1],_63[2],_63[3],_63[4],_63[6],_62);});},_64=function(_65,_66){var _67=E(_65);return new F(function(){return _5C(_67[1],_67[2],_67[3],_67[4],_67[6],_66);});},_68=44,_69=93,_6a=91,_6b=function(_6c,_6d,_6e){var _6f=E(_6d);if(!_6f[0]){return new F(function(){return unAppCStr("[]",_6e);});}else{var _6g=new T(function(){var _6h=new T(function(){var _6i=function(_6j){var _6k=E(_6j);if(!_6k[0]){return [1,_69,_6e];}else{var _6l=new T(function(){return B(A(_6c,[_6k[1],new T(function(){return B(_6i(_6k[2]));})]));});return [1,_68,_6l];}};return B(_6i(_6f[2]));});return B(A(_6c,[_6f[1],_6h]));});return [1,_6a,_6g];}},_6m=function(_6n,_6o){return new F(function(){return _6b(_64,_6n,_6o);});},_6p=[0,_5Z,_5W,_6m],_6q=new T(function(){return [0,_4W,_6p,_6r,_58,_5W];}),_6r=function(_6s){return [0,_6q,_6s];},_6t=[0],_6u=7,_6v=function(_6w){return [0,_6t,_6u,_3n,_6w,_6t,_6t];},_6x=function(_6y,_){var _6z=new T(function(){return B(_6r(new T(function(){return B(_6v(_6y));})));});return new F(function(){return die(_6z);});},_6A=[0,_4L,_4M,_4H,_4F,_6x],_6B=[0,_6A,_Q],_6C=[0,_6B,_4F],_6D=function(_6E,_6F,_6G,_6H,_6I,_6J,_6K,_6L){if(_6E!=_6I){return false;}else{if(E(_6F)!=E(_6J)){return false;}else{var _6M=E(_6G),_6N=E(_6K);if(E(_6M[1])!=E(_6N[1])){return false;}else{if(E(_6M[2])!=E(_6N[2])){return false;}else{return new F(function(){return _26(_6H,_6L);});}}}}},_6O=function(_6P,_6Q){var _6R=E(_6P),_6S=E(_6R[1]),_6T=E(_6Q),_6U=E(_6T[1]);return new F(function(){return _6D(E(_6S[1]),_6S[2],_6R[2],_6R[3],E(_6U[1]),_6U[2],_6T[2],_6T[3]);});},_6V="scans",_6W=[1,_6V,_3n],_6X="calib",_6Y=[1,_6X,_6W],_6Z=function(_70){var _71=E(_70);return [3,[1,new T(function(){return B(_2E(_71[1]));}),[1,new T(function(){return B(_2E(_71[2]));}),_3n]]];},_72=new T(function(){return [1,"Dragging"];}),_73=[0,_1T,_72],_74=new T(function(){return [1,"Free"];}),_75="state",_76=[0,_75,_74],_77=[1,_76,_3n],_78=[4,E(_77)],_79=function(_7a,_7b){switch(E(_7a)){case 0:return new F(function(){return _16(_24,_7b);});break;case 1:return new F(function(){return _16(_25,_7b);});break;case 2:return new F(function(){return _16(_22,_7b);});break;default:return new F(function(){return _16(_23,_7b);});}},_7c=function(_7d){return E(toJSStr(B(_79(_7d,_3n))));},_7e=function(_7f){return [1,B(_7c(_7f))];},_7g=function(_7h){var _7i=new T(function(){var _7j=E(E(_7h)[2]);return [3,[1,new T(function(){return B(_6Z(_7j[1]));}),[1,new T(function(){return B(_6Z(_7j[2]));}),[1,new T(function(){return B(_6Z(_7j[3]));}),[1,new T(function(){return B(_6Z(_7j[4]));}),_3n]]]]];}),_7k=new T(function(){var _7l=E(E(_7h)[1]);if(!_7l[0]){return E(_78);}else{return [4,[1,_73,[1,[0,_1O,new T(function(){return B(_7e(_7l[1]));})],_3n]]];}});return [1,[0,_1N,_7k],[1,[0,_1M,_7i],_3n]];},_7m="rotations",_7n=[1,_7m,_3n],_7o="choice",_7p=[1,_7o,_7n],_7q="offset",_7r=[1,_7q,_7p],_7s="bottom",_7t=[1,_7s,_7r],_7u="top",_7v=[1,_7u,_7t],_7w="fileName",_7x=[1,_7w,_7v],_7y="scans",_7z=[1,_7y,_7x],_7A="mouse",_7B=[1,_7A,_7z],_7C=function(_7D,_7E){var _7F=E(_7D);if(!_7F[0]){return [0];}else{var _7G=E(_7E);return (_7G[0]==0)?[0]:[1,[0,_7F[1],_7G[1]],new T(function(){return B(_7C(_7F[2],_7G[2]));})];}},_7H=function(_7I){return new F(function(){return _7C(_7B,[1,new T(function(){if(!E(E(_7I)[1])){return [1,toJSStr(E(_2Y))];}else{return [1,toJSStr(E(_2Z))];}}),[1,new T(function(){return [3,E(B(_1A(_3u,E(_7I)[2])))];}),[1,new T(function(){return [1,toJSStr(E(E(_7I)[3]))];}),[1,new T(function(){return [0,E(E(_7I)[4])];}),[1,new T(function(){return [0,E(E(_7I)[5])];}),[1,new T(function(){return [0,E(E(_7I)[6])];}),[1,new T(function(){if(!E(E(_7I)[7])){return [1,toJSStr(E(_2O))];}else{return [1,toJSStr(E(_2P))];}}),[1,new T(function(){return [3,E(B(_1A(_2E,E(_7I)[8])))];}),_3n]]]]]]]]);});},_7J=function(_7K){return [1,E(_7K)];},_7L="deltaZ",_7M="deltaY",_7N="deltaX",_7O=function(_7P,_7Q){var _7R=jsShowI(_7P);return new F(function(){return _16(fromJSStr(_7R),_7Q);});},_7S=41,_7T=40,_7U=function(_7V,_7W,_7X){if(_7W>=0){return new F(function(){return _7O(_7W,_7X);});}else{if(_7V<=6){return new F(function(){return _7O(_7W,_7X);});}else{return [1,_7T,new T(function(){var _7Y=jsShowI(_7W);return B(_16(fromJSStr(_7Y),[1,_7S,_7X]));})];}}},_7Z=new T(function(){return B(unCStr(")"));}),_80=new T(function(){return B(_7U(0,2,_7Z));}),_81=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_80));}),_82=function(_83){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_7U(0,_83,_81));}))));});},_84=function(_85,_){return new T(function(){var _86=Number(E(_85)),_87=jsTrunc(_86);if(_87<0){return B(_82(_87));}else{if(_87>2){return B(_82(_87));}else{return _87;}}});},_88=0,_89=[0,_88,_88,_88],_8a="button",_8b=new T(function(){return jsGetMouseCoords;}),_8c=function(_8d,_){var _8e=E(_8d);if(!_8e[0]){return _3n;}else{var _8f=B(_8c(_8e[2],_));return [1,new T(function(){var _8g=Number(E(_8e[1]));return jsTrunc(_8g);}),_8f];}},_8h=function(_8i,_){var _8j=__arr2lst(0,_8i);return new F(function(){return _8c(_8j,_);});},_8k=function(_8l,_){return new F(function(){return _8h(E(_8l),_);});},_8m=function(_8n,_){return new T(function(){var _8o=Number(E(_8n));return jsTrunc(_8o);});},_8p=[0,_8m,_8k],_8q=function(_8r,_){var _8s=E(_8r);if(!_8s[0]){return _3n;}else{var _8t=B(_8q(_8s[2],_));return [1,_8s[1],_8t];}},_8u=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_8v=[0,_6t,_6u,_3n,_8u,_6t,_6t],_8w=new T(function(){return B(_6r(_8v));}),_8x=function(_){return new F(function(){return die(_8w);});},_8y=function(_8z){return E(E(_8z)[1]);},_8A=function(_8B,_8C,_8D,_){var _8E=__arr2lst(0,_8D),_8F=B(_8q(_8E,_)),_8G=E(_8F);if(!_8G[0]){return new F(function(){return _8x(_);});}else{var _8H=E(_8G[2]);if(!_8H[0]){return new F(function(){return _8x(_);});}else{if(!E(_8H[2])[0]){var _8I=B(A(_8y,[_8B,_8G[1],_])),_8J=B(A(_8y,[_8C,_8H[1],_]));return [0,_8I,_8J];}else{return new F(function(){return _8x(_);});}}}},_8K=function(_){return new F(function(){return __jsNull();});},_8L=function(_8M){var _8N=B(A(_8M,[_]));return E(_8N);},_8O=new T(function(){return B(_8L(_8K));}),_8P=new T(function(){return E(_8O);}),_8Q=function(_8R,_8S,_){if(E(_8R)==7){var _8T=E(_8b)(_8S),_8U=B(_8A(_8p,_8p,_8T,_)),_8V=_8S[E(_7N)],_8W=_8S[E(_7M)],_8X=_8S[E(_7L)];return new T(function(){return [0,E(_8U),E(_6t),[0,_8V,_8W,_8X]];});}else{var _8Y=E(_8b)(_8S),_8Z=B(_8A(_8p,_8p,_8Y,_)),_90=_8S[E(_8a)],_91=__eq(_90,E(_8P));if(!E(_91)){var _92=B(_84(_90,_));return new T(function(){return [0,E(_8Z),[1,_92],E(_89)];});}else{return new T(function(){return [0,E(_8Z),E(_6t),E(_89)];});}}},_93=function(_94,_95,_){return new F(function(){return _8Q(_94,E(_95),_);});},_96="mouseout",_97="mouseover",_98="mousemove",_99="mouseup",_9a="mousedown",_9b="dblclick",_9c="click",_9d="wheel",_9e=function(_9f){switch(E(_9f)){case 0:return E(_9c);case 1:return E(_9b);case 2:return E(_9a);case 3:return E(_99);case 4:return E(_98);case 5:return E(_97);case 6:return E(_96);default:return E(_9d);}},_9g=[0,_9e,_93],_9h=function(_){return new F(function(){return E(_4)("td");});},_9i=function(_9j){return E(E(_9j)[1]);},_9k=function(_9l){return E(E(_9l)[3]);},_9m=function(_9n){return E(E(_9n)[2]);},_9o=function(_9p){return E(E(_9p)[4]);},_9q=(function(c,p){p.appendChild(c);}),_9r=function(_9s){return E(E(_9s)[1]);},_9t=(function(e,p,v){e.setAttribute(p, v);}),_9u=(function(e,p,v){e.style[p] = v;}),_9v=function(_9w,_9x,_9y,_9z){var _9A=new T(function(){return B(A(_9r,[_9w,_9y]));}),_9B=function(_9C,_){var _9D=E(_9C);if(!_9D[0]){return _a;}else{var _9E=E(_9A),_9F=E(_9q),_9G=_9F(E(_9D[1]),_9E),_9H=_9D[2];while(1){var _9I=E(_9H);if(!_9I[0]){return _a;}else{var _9J=_9F(E(_9I[1]),_9E);_9H=_9I[2];continue;}}}},_9K=function(_9L,_){while(1){var _9M=B((function(_9N,_){var _9O=E(_9N);if(!_9O[0]){return _a;}else{var _9P=_9O[2],_9Q=E(_9O[1]);if(!_9Q[0]){var _9R=_9Q[2],_9S=E(_9Q[1]);switch(_9S[0]){case 0:var _9T=E(_9A),_9U=E(_1),_9V=_9U(_9T,_9S[1],_9R),_9W=_9P;while(1){var _9X=E(_9W);if(!_9X[0]){return _a;}else{var _9Y=_9X[2],_9Z=E(_9X[1]);if(!_9Z[0]){var _a0=_9Z[2],_a1=E(_9Z[1]);switch(_a1[0]){case 0:var _a2=_9U(_9T,_a1[1],_a0);_9W=_9Y;continue;case 1:var _a3=E(_9u)(_9T,_a1[1],_a0);_9W=_9Y;continue;default:var _a4=E(_9t)(_9T,_a1[1],_a0);_9W=_9Y;continue;}}else{var _a5=B(_9B(_9Z[1],_));_9W=_9Y;continue;}}}break;case 1:var _a6=E(_9A),_a7=E(_9u),_a8=_a7(_a6,_9S[1],_9R),_a9=_9P;while(1){var _aa=E(_a9);if(!_aa[0]){return _a;}else{var _ab=_aa[2],_ac=E(_aa[1]);if(!_ac[0]){var _ad=_ac[2],_ae=E(_ac[1]);switch(_ae[0]){case 0:var _af=E(_1)(_a6,_ae[1],_ad);_a9=_ab;continue;case 1:var _ag=_a7(_a6,_ae[1],_ad);_a9=_ab;continue;default:var _ah=E(_9t)(_a6,_ae[1],_ad);_a9=_ab;continue;}}else{var _ai=B(_9B(_ac[1],_));_a9=_ab;continue;}}}break;default:var _aj=E(_9A),_ak=E(_9t),_al=_ak(_aj,_9S[1],_9R),_am=_9P;while(1){var _an=E(_am);if(!_an[0]){return _a;}else{var _ao=_an[2],_ap=E(_an[1]);if(!_ap[0]){var _aq=_ap[2],_ar=E(_ap[1]);switch(_ar[0]){case 0:var _as=E(_1)(_aj,_ar[1],_aq);_am=_ao;continue;case 1:var _at=E(_9u)(_aj,_ar[1],_aq);_am=_ao;continue;default:var _au=_ak(_aj,_ar[1],_aq);_am=_ao;continue;}}else{var _av=B(_9B(_ap[1],_));_am=_ao;continue;}}}}}else{var _aw=B(_9B(_9Q[1],_));_9L=_9P;return null;}}})(_9L,_));if(_9M!=null){return _9M;}}};return new F(function(){return A(_2,[_9x,function(_){return new F(function(){return _9K(_9z,_);});}]);});},_ax=function(_ay,_az,_aA,_aB){var _aC=B(_9i(_az)),_aD=function(_aE){return new F(function(){return A(_9k,[_aC,new T(function(){return B(_9v(_ay,_az,_aE,_aB));}),new T(function(){return B(A(_9o,[_aC,_aE]));})]);});};return new F(function(){return A(_9m,[_aC,_aA,_aD]);});},_aF=function(_aG,_){var _aH=E(_aG);if(!_aH[0]){return _3n;}else{var _aI=B(A(_ax,[_S,_6B,_9h,[1,[1,[1,_aH[1],_3n]],_3n],_])),_aJ=B(_aF(_aH[2],_));return [1,_aI,_aJ];}},_aK=function(_aL,_aM,_){var _aN=B(A(_ax,[_S,_6B,_9h,[1,[1,[1,_aL,_3n]],_3n],_])),_aO=B(_aF(_aM,_));return [1,_aN,_aO];},_aP=(function(s){return document.createTextNode(s);}),_aQ=function(_aR,_){var _aS=jsShow(_aR),_aT=E(_aP)(toJSStr(fromJSStr(_aS)));return new F(function(){return A(_ax,[_S,_6B,_9h,[1,[1,[1,_aT,_3n]],_3n],_]);});},_aU=function(_aV,_aW){var _aX=(_aW-_aV)*25/900;if(!_aX){var _aY=rintDouble(0);return _aY&4294967295;}else{if(_aX<=0){var _aZ=rintDouble( -_aX/0.1);return _aZ&4294967295;}else{var _b0=rintDouble(_aX/0.1);return _b0&4294967295;}}},_b1=function(_b2,_b3){return [0,E(_b2),toJSStr(E(_b3))];},_b4=2,_b5=0,_b6=new T(function(){return B(unCStr("x1"));}),_b7=new T(function(){return B(unCStr("y1"));}),_b8=new T(function(){return B(unCStr("x2"));}),_b9=new T(function(){return B(unCStr("y2"));}),_ba=new T(function(){return B(unCStr("frames"));}),_bb=new T(function(){return B(unCStr("time (minutes)"));}),_bc=new T(function(){return B(unCStr("title"));}),_bd=new T(function(){return B(unCStr("Delete"));}),_be=[1,_bd,_3n],_bf=[1,_bc,_be],_bg=[1,_bb,_bf],_bh=[1,_ba,_bg],_bi=[1,_b9,_bh],_bj=[1,_b8,_bi],_bk=function(_){return new F(function(){return E(_4)("span");});},_bl=new T(function(){return [0,[2,"class"],"glyphicon glyphicon-remove"];}),_bm=[1,_bl,_3n],_bn=new T(function(){return B(_ax(_S,_6B,_bk,_bm));}),_bo=function(_){return new F(function(){return E(_4)("input");});},_bp=function(_){return new F(function(){return E(_4)("tr");});},_bq=function(_){return new F(function(){return E(_4)("th");});},_br=function(_){return new F(function(){return E(_4)("button");});},_bs=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_bt=function(_bu){var _bv=I_decodeDouble(_bu);return [0,[1,_bv[2]],_bv[1]];},_bw=function(_bx){var _by=E(_bx);if(!_by[0]){return _by[1];}else{return new F(function(){return I_toNumber(_by[1]);});}},_bz=function(_bA){return [0,_bA];},_bB=function(_bC){var _bD=hs_intToInt64(2147483647),_bE=hs_leInt64(_bC,_bD);if(!_bE){return [1,I_fromInt64(_bC)];}else{var _bF=hs_intToInt64(-2147483648),_bG=hs_geInt64(_bC,_bF);if(!_bG){return [1,I_fromInt64(_bC)];}else{var _bH=hs_int64ToInt(_bC);return new F(function(){return _bz(_bH);});}}},_bI=function(_bJ){var _bK=hs_intToInt64(_bJ);return E(_bK);},_bL=function(_bM){var _bN=E(_bM);if(!_bN[0]){return new F(function(){return _bI(_bN[1]);});}else{return new F(function(){return I_toInt64(_bN[1]);});}},_bO=new T(function(){return [2,"value"];}),_bP=new T(function(){return [0,[2,"type"],"text"];}),_bQ=new T(function(){return [0,[2,"class"],"btn btn-danger"];}),_bR=function(_bS){return E(E(_bS)[1]);},_bT=function(_bU){return E(E(_bU)[2]);},_bV=function(_bW){return E(E(_bW)[1]);},_bX=function(_){return new F(function(){return nMV(_6t);});},_bY=new T(function(){return B(_8L(_bX));}),_bZ=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_c0=function(_c1){return E(E(_c1)[2]);},_c2=function(_c3,_c4,_c5,_c6,_c7,_c8){var _c9=B(_bR(_c3)),_ca=B(_9i(_c9)),_cb=new T(function(){return B(_2(_c9));}),_cc=new T(function(){return B(_9o(_ca));}),_cd=new T(function(){return B(A(_9r,[_c4,_c6]));}),_ce=new T(function(){return B(A(_bV,[_c5,_c7]));}),_cf=function(_cg){return new F(function(){return A(_cc,[[0,_ce,_cd,_cg]]);});},_ch=function(_ci){var _cj=new T(function(){var _ck=new T(function(){var _cl=__createJSFunc(2,function(_cm,_){var _cn=B(A(E(_ci),[_cm,_]));return _8P;}),_co=_cl;return function(_){return new F(function(){return E(_bZ)(E(_cd),E(_ce),_co);});};});return B(A(_cb,[_ck]));});return new F(function(){return A(_9m,[_ca,_cj,_cf]);});},_cp=new T(function(){var _cq=new T(function(){return B(_2(_c9));}),_cr=function(_cs){var _ct=new T(function(){return B(A(_cq,[function(_){var _=wMV(E(_bY),[1,_cs]);return new F(function(){return A(_bT,[_c5,_c7,_cs,_]);});}]));});return new F(function(){return A(_9m,[_ca,_ct,_c8]);});};return B(A(_c0,[_c3,_cr]));});return new F(function(){return A(_9m,[_ca,_cp,_ch]);});},_cu=function(_cv,_cw){while(1){var _cx=E(_cv);if(!_cx[0]){return E(_cw);}else{var _cy=[1,_cx[1],_cw];_cv=_cx[2];_cw=_cy;continue;}}},_cz=function(_cA,_cB){while(1){var _cC=E(_cA);if(!_cC[0]){_cA=[1,I_fromInt(_cC[1])];continue;}else{return [1,I_shiftLeft(_cC[1],_cB)];}}},_cD=function(_cE,_cF,_cG,_cH,_){var _cI=E(_bs)(_cH),_cJ=E(_aP),_cK=_cJ(toJSStr(E(_b6))),_cL=B(A(_ax,[_S,_6B,_bq,[1,[1,[1,_cK,_3n]],_3n],_])),_cM=function(_cN,_){var _cO=E(_cN);if(!_cO[0]){return _3n;}else{var _cP=_cJ(toJSStr(E(_cO[1]))),_cQ=B(A(_ax,[_S,_6B,_bq,[1,[1,[1,_cP,_3n]],_3n],_])),_cR=B(_cM(_cO[2],_));return [1,_cQ,_cR];}},_cS=B((function(_cT,_cU,_){var _cV=_cJ(toJSStr(E(_cT))),_cW=B(A(_ax,[_S,_6B,_bq,[1,[1,[1,_cV,_3n]],_3n],_])),_cX=B(_cM(_cU,_));return [1,_cW,_cX];})(_b7,_bj,_)),_cY=B(A(_ax,[_S,_6B,_bp,[1,[1,[1,_cL,_cS]],_3n],_])),_cZ=E(_9q),_d0=_cZ(E(_cY),_cH),_d1=function(_d2,_){var _d3=E(_d2);if(!_d3[0]){return _3n;}else{var _d4=E(_d3[1]),_d5=E(_d4[1]),_d6=E(_d4[2]),_d7=E(_d5[1]),_d8=B(_aQ(_d7*25/900,_)),_d9=_d8,_da=E(_d5[2]),_db=B(_aQ(_da*25/900,_)),_dc=_db,_dd=E(_d6[1]),_de=B(_aQ(_dd*25/900,_)),_df=_de,_dg=E(_d6[2]),_dh=B(_aQ(_dg*25/900,_)),_di=_dh,_dj=function(_dk){var _dl=B(_aQ(_dk,_)),_dm=_dl,_dn=function(_do){var _dp=rintDouble(_do*5.8333333333333334e-2),_dq=B(_bt(_dp)),_dr=_dq[1],_ds=_dq[2],_dt=function(_du){var _dv=B(_aQ(_du,_)),_dw=B(_aK(_d9,[1,_dc,[1,_df,[1,_di,[1,_dm,[1,_dv,_3n]]]]],_)),_dx=B(A(_ax,[_S,_6B,_bp,[1,new T(function(){return B(_7J(_dw));}),_3n],_])),_dy=B(A(_ax,[_S,_6B,_bo,[1,_bP,[1,new T(function(){return B(_b1(_bO,_d4[3]));}),_3n]],_])),_dz=B(A(_bn,[_])),_dA=B(A(_ax,[_S,_6B,_br,[1,_bQ,[1,[1,[1,_dz,_3n]],_3n]],_])),_dB=B(A(_ax,[_S,_6B,_9h,[1,[1,[1,_dy,_3n]],_3n],_])),_dC=E(_dx),_dD=_cZ(E(_dB),_dC),_dE=E(_dA),_dF=_cZ(_dE,_dC),_dG=new T(function(){return B(A(_cF,[_d4]));}),_dH=B(A(_c2,[_6C,_S,_9g,_dE,_b5,function(_dI){return E(_dG);},_])),_dJ=new T(function(){return B(A(_cE,[_dy,_d4]));}),_dK=B(A(_c2,[_6C,_S,_o,_dy,_b4,function(_dL){return E(_dJ);},_])),_dM=_cZ(_dC,_cH),_dN=B(_d1(_d3[2],_));return [1,_a,_dN];};if(_ds>=0){return new F(function(){return _dt(B(_bw(B(_cz(_dr,_ds)))));});}else{var _dO=hs_uncheckedIShiftRA64(B(_bL(_dr)), -_ds);return new F(function(){return _dt(B(_bw(B(_bB(_dO)))));});}};if(_d7!=_dd){return new F(function(){return _dn(B(_aU(_d7,_dd)));});}else{return new F(function(){return _dn(B(_aU(_da,_dg)));});}};if(_d7!=_dd){return new F(function(){return _dj(B(_aU(_d7,_dd)));});}else{return new F(function(){return _dj(B(_aU(_da,_dg)));});}}},_dP=B(_d1(B(_cu(E(_cG)[2],_3n)),_));return _a;},_dQ=function(_){return _a;},_dR=(function(ctx){ctx.restore();}),_dS=(function(ctx){ctx.save();}),_dT=(function(ctx,x,y){ctx.scale(x,y);}),_dU=function(_dV,_dW,_dX,_dY,_){var _dZ=E(_dS)(_dY),_e0=E(_dT)(_dY,E(_dV),E(_dW)),_e1=B(A(_dX,[_dY,_])),_e2=E(_dR)(_dY);return new F(function(){return _dQ(_);});},_e3=(function(ctx){ctx.beginPath();}),_e4=(function(ctx){ctx.stroke();}),_e5=function(_e6,_e7,_){var _e8=E(_e3)(_e7),_e9=B(A(_e6,[_e7,_])),_ea=E(_e4)(_e7);return new F(function(){return _dQ(_);});},_eb=(function(ctx,i,x,y){ctx.drawImage(i,x,y);}),_ec=function(_ed,_ee,_ef,_eg,_){var _eh=E(_eb)(_eg,_ed,_ee,_ef);return new F(function(){return _dQ(_);});},_ei=",",_ej="[",_ek="]",_el="{",_em="}",_en=":",_eo="\"",_ep="true",_eq="false",_er="null",_es=new T(function(){return JSON.stringify;}),_et=function(_eu,_ev){var _ew=E(_ev);switch(_ew[0]){case 0:return [0,new T(function(){return jsShow(_ew[1]);}),_eu];case 1:return [0,new T(function(){var _ex=E(_es)(_ew[1]);return String(_ex);}),_eu];case 2:return (!E(_ew[1]))?[0,_eq,_eu]:[0,_ep,_eu];case 3:var _ey=E(_ew[1]);if(!_ey[0]){return [0,_ej,[1,_ek,_eu]];}else{var _ez=new T(function(){var _eA=new T(function(){var _eB=function(_eC){var _eD=E(_eC);if(!_eD[0]){return [1,_ek,_eu];}else{var _eE=new T(function(){var _eF=B(_et(new T(function(){return B(_eB(_eD[2]));}),_eD[1]));return [1,_eF[1],_eF[2]];});return [1,_ei,_eE];}};return B(_eB(_ey[2]));}),_eG=B(_et(_eA,_ey[1]));return [1,_eG[1],_eG[2]];});return [0,_ej,_ez];}break;case 4:var _eH=E(_ew[1]);if(!_eH[0]){return [0,_el,[1,_em,_eu]];}else{var _eI=E(_eH[1]),_eJ=new T(function(){var _eK=new T(function(){var _eL=function(_eM){var _eN=E(_eM);if(!_eN[0]){return [1,_em,_eu];}else{var _eO=E(_eN[1]),_eP=new T(function(){var _eQ=B(_et(new T(function(){return B(_eL(_eN[2]));}),_eO[2]));return [1,_eQ[1],_eQ[2]];});return [1,_ei,[1,_eo,[1,_eO[1],[1,_eo,[1,_en,_eP]]]]];}};return B(_eL(_eH[2]));}),_eR=B(_et(_eK,_eI[2]));return [1,_eR[1],_eR[2]];});return [0,_el,[1,new T(function(){var _eS=E(_es)(E(_eI[1]));return String(_eS);}),[1,_en,_eJ]]];}break;default:return [0,_er,_eu];}},_eT=new T(function(){return toJSStr(_3n);}),_eU=function(_eV){var _eW=B(_et(_3n,_eV)),_eX=jsCat([1,_eW[1],_eW[2]],E(_eT));return E(_eX);},_eY=function(_eZ,_f0){return E(_eZ)!=E(_f0);},_f1=function(_f2,_f3){return E(_f2)==E(_f3);},_f4=[0,_f1,_eY],_f5=function(_f6,_f7,_f8){while(1){var _f9=E(_f8);if(!_f9[0]){return false;}else{if(!B(A(_T,[_f6,_f7,_f9[1]]))){_f8=_f9[2];continue;}else{return true;}}}},_fa=32,_fb=function(_fc){while(1){var _fd=E(_fc);if(!_fd[0]){return false;}else{var _fe=E(_fd[1]);if(!_fe[0]){return true;}else{if(!B(_f5(_f4,_fa,_fe))){_fc=_fd[2];continue;}else{return true;}}}}},_ff=function(_fg){return E(E(_fg)[3]);},_fh=function(_fi,_fj,_fk){var _fl=E(_fi);return (_fl[0]==0)?false:(!B(_fb(B(_1A(_ff,_fl)))))?(!B(_26(_fj,_3n)))?(!B(_f5(_f4,_fa,_fj)))?(E(_fk)[0]==0)?false:true:false:false:false;},_fm=function(_fn){while(1){var _fo=E(_fn);if(!_fo[0]){_fn=[1,I_fromInt(_fo[1])];continue;}else{return new F(function(){return I_toString(_fo[1]);});}}},_fp=function(_fq,_fr){return new F(function(){return _16(fromJSStr(B(_fm(_fq))),_fr);});},_fs=function(_ft,_fu){var _fv=E(_ft);if(!_fv[0]){var _fw=_fv[1],_fx=E(_fu);return (_fx[0]==0)?_fw<_fx[1]:I_compareInt(_fx[1],_fw)>0;}else{var _fy=_fv[1],_fz=E(_fu);return (_fz[0]==0)?I_compareInt(_fy,_fz[1])<0:I_compare(_fy,_fz[1])<0;}},_fA=[0,0],_fB=function(_fC,_fD,_fE){if(_fC<=6){return new F(function(){return _fp(_fD,_fE);});}else{if(!B(_fs(_fD,_fA))){return new F(function(){return _fp(_fD,_fE);});}else{return [1,_7T,new T(function(){return B(_16(fromJSStr(B(_fm(_fD))),[1,_7S,_fE]));})];}}},_fF=0,_fG=1,_fH=function(_fI){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_fI));}))));});},_fJ=new T(function(){return B(_fH("ww_syQh MouseState"));}),_fK=new T(function(){return B(_fH("ww_syQj String"));}),_fL=function(_fM){var _fN=E(_fM);if(!_fN[0]){return [0];}else{return new F(function(){return _16(_fN[1],new T(function(){return B(_fL(_fN[2]));},1));});}},_fO=new T(function(){return B(unCStr("\r\n"));}),_fP=new T(function(){return B(_16(_fO,_fO));}),_fQ=function(_fR,_fS){var _fT=E(_fS);return (_fT[0]==0)?[0]:[1,_fR,[1,_fT[1],new T(function(){return B(_fQ(_fR,_fT[2]));})]];},_fU=new T(function(){return B(unCStr("printf: formatting string ended prematurely"));}),_fV=new T(function(){return B(err(_fU));}),_fW=function(_fX,_fY){var _fZ=E(_fY);return (_fZ[0]==0)?E(_fV):[0,_3n,_fZ[1],_fZ[2]];},_g0=new T(function(){return B(unCStr("ACK"));}),_g1=new T(function(){return B(unCStr("BEL"));}),_g2=new T(function(){return B(unCStr("BS"));}),_g3=new T(function(){return B(unCStr("SP"));}),_g4=[1,_g3,_3n],_g5=new T(function(){return B(unCStr("US"));}),_g6=[1,_g5,_g4],_g7=new T(function(){return B(unCStr("RS"));}),_g8=[1,_g7,_g6],_g9=new T(function(){return B(unCStr("GS"));}),_ga=[1,_g9,_g8],_gb=new T(function(){return B(unCStr("FS"));}),_gc=[1,_gb,_ga],_gd=new T(function(){return B(unCStr("ESC"));}),_ge=[1,_gd,_gc],_gf=new T(function(){return B(unCStr("SUB"));}),_gg=[1,_gf,_ge],_gh=new T(function(){return B(unCStr("EM"));}),_gi=[1,_gh,_gg],_gj=new T(function(){return B(unCStr("CAN"));}),_gk=[1,_gj,_gi],_gl=new T(function(){return B(unCStr("ETB"));}),_gm=[1,_gl,_gk],_gn=new T(function(){return B(unCStr("SYN"));}),_go=[1,_gn,_gm],_gp=new T(function(){return B(unCStr("NAK"));}),_gq=[1,_gp,_go],_gr=new T(function(){return B(unCStr("DC4"));}),_gs=[1,_gr,_gq],_gt=new T(function(){return B(unCStr("DC3"));}),_gu=[1,_gt,_gs],_gv=new T(function(){return B(unCStr("DC2"));}),_gw=[1,_gv,_gu],_gx=new T(function(){return B(unCStr("DC1"));}),_gy=[1,_gx,_gw],_gz=new T(function(){return B(unCStr("DLE"));}),_gA=[1,_gz,_gy],_gB=new T(function(){return B(unCStr("SI"));}),_gC=[1,_gB,_gA],_gD=new T(function(){return B(unCStr("SO"));}),_gE=[1,_gD,_gC],_gF=new T(function(){return B(unCStr("CR"));}),_gG=[1,_gF,_gE],_gH=new T(function(){return B(unCStr("FF"));}),_gI=[1,_gH,_gG],_gJ=new T(function(){return B(unCStr("VT"));}),_gK=[1,_gJ,_gI],_gL=new T(function(){return B(unCStr("LF"));}),_gM=[1,_gL,_gK],_gN=new T(function(){return B(unCStr("HT"));}),_gO=[1,_gN,_gM],_gP=[1,_g2,_gO],_gQ=[1,_g1,_gP],_gR=[1,_g0,_gQ],_gS=new T(function(){return B(unCStr("ENQ"));}),_gT=[1,_gS,_gR],_gU=new T(function(){return B(unCStr("EOT"));}),_gV=[1,_gU,_gT],_gW=new T(function(){return B(unCStr("ETX"));}),_gX=[1,_gW,_gV],_gY=new T(function(){return B(unCStr("STX"));}),_gZ=[1,_gY,_gX],_h0=new T(function(){return B(unCStr("SOH"));}),_h1=[1,_h0,_gZ],_h2=new T(function(){return B(unCStr("NUL"));}),_h3=[1,_h2,_h1],_h4=92,_h5=new T(function(){return B(unCStr("\\DEL"));}),_h6=new T(function(){return B(unCStr("\\a"));}),_h7=new T(function(){return B(unCStr("\\\\"));}),_h8=new T(function(){return B(unCStr("\\SO"));}),_h9=new T(function(){return B(unCStr("\\r"));}),_ha=new T(function(){return B(unCStr("\\f"));}),_hb=new T(function(){return B(unCStr("\\v"));}),_hc=new T(function(){return B(unCStr("\\n"));}),_hd=new T(function(){return B(unCStr("\\t"));}),_he=new T(function(){return B(unCStr("\\b"));}),_hf=function(_hg,_hh){if(_hg<=127){var _hi=E(_hg);switch(_hi){case 92:return new F(function(){return _16(_h7,_hh);});break;case 127:return new F(function(){return _16(_h5,_hh);});break;default:if(_hi<32){var _hj=E(_hi);switch(_hj){case 7:return new F(function(){return _16(_h6,_hh);});break;case 8:return new F(function(){return _16(_he,_hh);});break;case 9:return new F(function(){return _16(_hd,_hh);});break;case 10:return new F(function(){return _16(_hc,_hh);});break;case 11:return new F(function(){return _16(_hb,_hh);});break;case 12:return new F(function(){return _16(_ha,_hh);});break;case 13:return new F(function(){return _16(_h9,_hh);});break;case 14:return new F(function(){return _16(_h8,new T(function(){var _hk=E(_hh);if(!_hk[0]){return [0];}else{if(E(_hk[1])==72){return B(unAppCStr("\\&",_hk));}else{return E(_hk);}}},1));});break;default:return new F(function(){return _16([1,_h4,new T(function(){return B(_1m(_h3,_hj));})],_hh);});}}else{return [1,_hi,_hh];}}}else{var _hl=new T(function(){var _hm=jsShowI(_hg);return B(_16(fromJSStr(_hm),new T(function(){var _hn=E(_hh);if(!_hn[0]){return [0];}else{var _ho=E(_hn[1]);if(_ho<48){return E(_hn);}else{if(_ho>57){return E(_hn);}else{return B(unAppCStr("\\&",_hn));}}}},1)));});return [1,_h4,_hl];}},_hp=39,_hq=[1,_hp,_3n],_hr=new T(function(){return B(unCStr("\'\\\'\'"));}),_hs=new T(function(){return B(_16(_hr,_3n));}),_ht=function(_hu){var _hv=new T(function(){var _hw=new T(function(){var _hx=E(_hu);if(_hx==39){return E(_hs);}else{return [1,_hp,new T(function(){return B(_hf(_hx,_hq));})];}});return B(unAppCStr("bad formatting char ",_hw));});return new F(function(){return err(B(unAppCStr("printf: ",_hv)));});},_hy=new T(function(){return B(unCStr("-"));}),_hz=new T(function(){return B(unCStr("printf: internal error: impossible dfmt"));}),_hA=new T(function(){return B(err(_hz));}),_hB=function(_hC){var _hD=E(_hC);return new F(function(){return Math.log(_hD+(_hD+1)*Math.sqrt((_hD-1)/(_hD+1)));});},_hE=function(_hF){var _hG=E(_hF);return new F(function(){return Math.log(_hG+Math.sqrt(1+_hG*_hG));});},_hH=function(_hI){var _hJ=E(_hI);return 0.5*Math.log((1+_hJ)/(1-_hJ));},_hK=function(_hL,_hM){return Math.log(E(_hM))/Math.log(E(_hL));},_hN=3.141592653589793,_hO=[0,1],_hP=function(_hQ,_hR){var _hS=E(_hQ);if(!_hS[0]){var _hT=_hS[1],_hU=E(_hR);if(!_hU[0]){var _hV=_hU[1];return (_hT!=_hV)?(_hT>_hV)?2:0:1;}else{var _hW=I_compareInt(_hU[1],_hT);return (_hW<=0)?(_hW>=0)?1:2:0;}}else{var _hX=_hS[1],_hY=E(_hR);if(!_hY[0]){var _hZ=I_compareInt(_hX,_hY[1]);return (_hZ>=0)?(_hZ<=0)?1:2:0;}else{var _i0=I_compare(_hX,_hY[1]);return (_i0>=0)?(_i0<=0)?1:2:0;}}},_i1=new T(function(){return B(unCStr("GHC.Exception"));}),_i2=new T(function(){return B(unCStr("base"));}),_i3=new T(function(){return B(unCStr("ArithException"));}),_i4=new T(function(){var _i5=hs_wordToWord64(4194982440),_i6=hs_wordToWord64(3110813675);return [0,_i5,_i6,[0,_i5,_i6,_i2,_i1,_i3],_3n,_3n];}),_i7=function(_i8){return E(_i4);},_i9=function(_ia){var _ib=E(_ia);return new F(function(){return _50(B(_4Y(_ib[1])),_i7,_ib[2]);});},_ic=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_id=new T(function(){return B(unCStr("denormal"));}),_ie=new T(function(){return B(unCStr("divide by zero"));}),_if=new T(function(){return B(unCStr("loss of precision"));}),_ig=new T(function(){return B(unCStr("arithmetic underflow"));}),_ih=new T(function(){return B(unCStr("arithmetic overflow"));}),_ii=function(_ij,_ik){switch(E(_ij)){case 0:return new F(function(){return _16(_ih,_ik);});break;case 1:return new F(function(){return _16(_ig,_ik);});break;case 2:return new F(function(){return _16(_if,_ik);});break;case 3:return new F(function(){return _16(_ie,_ik);});break;case 4:return new F(function(){return _16(_id,_ik);});break;default:return new F(function(){return _16(_ic,_ik);});}},_il=function(_im){return new F(function(){return _ii(_im,_3n);});},_in=function(_io,_ip,_iq){return new F(function(){return _ii(_ip,_iq);});},_ir=function(_is,_it){return new F(function(){return _6b(_ii,_is,_it);});},_iu=[0,_in,_il,_ir],_iv=new T(function(){return [0,_i7,_iu,_iw,_i9,_il];}),_iw=function(_ix){return [0,_iv,_ix];},_iy=3,_iz=new T(function(){return B(_iw(_iy));}),_iA=new T(function(){return die(_iz);}),_iB=function(_iC,_iD){var _iE=E(_iC);return (_iE[0]==0)?_iE[1]*Math.pow(2,_iD):I_toNumber(_iE[1])*Math.pow(2,_iD);},_iF=function(_iG,_iH){var _iI=E(_iG);if(!_iI[0]){var _iJ=_iI[1],_iK=E(_iH);return (_iK[0]==0)?_iJ==_iK[1]:(I_compareInt(_iK[1],_iJ)==0)?true:false;}else{var _iL=_iI[1],_iM=E(_iH);return (_iM[0]==0)?(I_compareInt(_iL,_iM[1])==0)?true:false:(I_compare(_iL,_iM[1])==0)?true:false;}},_iN=function(_iO){var _iP=E(_iO);if(!_iP[0]){return E(_iP[1]);}else{return new F(function(){return I_toInt(_iP[1]);});}},_iQ=function(_iR,_iS){while(1){var _iT=E(_iR);if(!_iT[0]){var _iU=_iT[1],_iV=E(_iS);if(!_iV[0]){var _iW=_iV[1],_iX=addC(_iU,_iW);if(!E(_iX[2])){return [0,_iX[1]];}else{_iR=[1,I_fromInt(_iU)];_iS=[1,I_fromInt(_iW)];continue;}}else{_iR=[1,I_fromInt(_iU)];_iS=_iV;continue;}}else{var _iY=E(_iS);if(!_iY[0]){_iR=_iT;_iS=[1,I_fromInt(_iY[1])];continue;}else{return [1,I_add(_iT[1],_iY[1])];}}}},_iZ=function(_j0,_j1){while(1){var _j2=E(_j0);if(!_j2[0]){var _j3=E(_j2[1]);if(_j3==(-2147483648)){_j0=[1,I_fromInt(-2147483648)];continue;}else{var _j4=E(_j1);if(!_j4[0]){var _j5=_j4[1];return [0,[0,quot(_j3,_j5)],[0,_j3%_j5]];}else{_j0=[1,I_fromInt(_j3)];_j1=_j4;continue;}}}else{var _j6=E(_j1);if(!_j6[0]){_j0=_j2;_j1=[1,I_fromInt(_j6[1])];continue;}else{var _j7=I_quotRem(_j2[1],_j6[1]);return [0,[1,_j7[1]],[1,_j7[2]]];}}}},_j8=[0,0],_j9=function(_ja,_jb,_jc){if(!B(_iF(_jc,_j8))){var _jd=B(_iZ(_jb,_jc)),_je=_jd[1];switch(B(_hP(B(_cz(_jd[2],1)),_jc))){case 0:return new F(function(){return _iB(_je,_ja);});break;case 1:if(!(B(_iN(_je))&1)){return new F(function(){return _iB(_je,_ja);});}else{return new F(function(){return _iB(B(_iQ(_je,_hO)),_ja);});}break;default:return new F(function(){return _iB(B(_iQ(_je,_hO)),_ja);});}}else{return E(_iA);}},_jf=function(_jg,_jh){var _ji=E(_jg);if(!_ji[0]){var _jj=_ji[1],_jk=E(_jh);return (_jk[0]==0)?_jj>_jk[1]:I_compareInt(_jk[1],_jj)<0;}else{var _jl=_ji[1],_jm=E(_jh);return (_jm[0]==0)?I_compareInt(_jl,_jm[1])>0:I_compare(_jl,_jm[1])>0;}},_jn=[0,1],_jo=new T(function(){return B(unCStr("Control.Exception.Base"));}),_jp=new T(function(){return B(unCStr("base"));}),_jq=new T(function(){return B(unCStr("PatternMatchFail"));}),_jr=new T(function(){var _js=hs_wordToWord64(18445595),_jt=hs_wordToWord64(52003073);return [0,_js,_jt,[0,_js,_jt,_jp,_jo,_jq],_3n,_3n];}),_ju=function(_jv){return E(_jr);},_jw=function(_jx){var _jy=E(_jx);return new F(function(){return _50(B(_4Y(_jy[1])),_ju,_jy[2]);});},_jz=function(_jA){return E(E(_jA)[1]);},_jB=function(_jC){return [0,_jD,_jC];},_jE=function(_jF,_jG){return new F(function(){return _16(E(_jF)[1],_jG);});},_jH=function(_jI,_jJ){return new F(function(){return _6b(_jE,_jI,_jJ);});},_jK=function(_jL,_jM,_jN){return new F(function(){return _16(E(_jM)[1],_jN);});},_jO=[0,_jK,_jz,_jH],_jD=new T(function(){return [0,_ju,_jO,_jB,_jw,_jz];}),_jP=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_jQ=function(_jR){return E(E(_jR)[3]);},_jS=function(_jT,_jU){return new F(function(){return die(new T(function(){return B(A(_jQ,[_jU,_jT]));}));});},_jV=function(_jW,_ix){return new F(function(){return _jS(_jW,_ix);});},_jX=function(_jY,_jZ){var _k0=E(_jZ);if(!_k0[0]){return [0,_3n,_3n];}else{var _k1=_k0[1];if(!B(A(_jY,[_k1]))){return [0,_3n,_k0];}else{var _k2=new T(function(){var _k3=B(_jX(_jY,_k0[2]));return [0,_k3[1],_k3[2]];});return [0,[1,_k1,new T(function(){return E(E(_k2)[1]);})],new T(function(){return E(E(_k2)[2]);})];}}},_k4=32,_k5=new T(function(){return B(unCStr("\n"));}),_k6=function(_k7){return (E(_k7)==124)?false:true;},_k8=function(_k9,_ka){var _kb=B(_jX(_k6,B(unCStr(_k9)))),_kc=_kb[1],_kd=function(_ke,_kf){var _kg=new T(function(){var _kh=new T(function(){return B(_16(_ka,new T(function(){return B(_16(_kf,_k5));},1)));});return B(unAppCStr(": ",_kh));},1);return new F(function(){return _16(_ke,_kg);});},_ki=E(_kb[2]);if(!_ki[0]){return new F(function(){return _kd(_kc,_3n);});}else{if(E(_ki[1])==124){return new F(function(){return _kd(_kc,[1,_k4,_ki[2]]);});}else{return new F(function(){return _kd(_kc,_3n);});}}},_kj=function(_kk){return new F(function(){return _jV([0,new T(function(){return B(_k8(_kk,_jP));})],_jD);});},_kl=function(_km){var _kn=_jn,_ko=0;while(1){if(!B(_fs(_kn,_km))){if(!B(_jf(_kn,_km))){if(!B(_iF(_kn,_km))){return new F(function(){return _kj("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ko);}}else{return _ko-1|0;}}else{var _kp=B(_cz(_kn,1)),_kq=_ko+1|0;_kn=_kp;_ko=_kq;continue;}}},_kr=function(_ks){var _kt=E(_ks);if(!_kt[0]){var _ku=_kt[1]>>>0;if(!_ku){return -1;}else{var _kv=1,_kw=0;while(1){if(_kv>=_ku){if(_kv<=_ku){if(_kv!=_ku){return new F(function(){return _kj("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_kw);}}else{return _kw-1|0;}}else{var _kx=imul(_kv,2)>>>0,_ky=_kw+1|0;_kv=_kx;_kw=_ky;continue;}}}}else{return new F(function(){return _kl(_kt);});}},_kz=function(_kA){var _kB=E(_kA);if(!_kB[0]){var _kC=_kB[1]>>>0;if(!_kC){return [0,-1,0];}else{var _kD=function(_kE,_kF){while(1){if(_kE>=_kC){if(_kE<=_kC){if(_kE!=_kC){return new F(function(){return _kj("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_kF);}}else{return _kF-1|0;}}else{var _kG=imul(_kE,2)>>>0,_kH=_kF+1|0;_kE=_kG;_kF=_kH;continue;}}};return [0,B(_kD(1,0)),(_kC&_kC-1>>>0)>>>0&4294967295];}}else{var _kI=B(_kr(_kB)),_kJ=_kI>>>0;if(!_kJ){var _kK=E(_kI);return (_kK==(-2))?[0,-2,0]:[0,_kK,1];}else{var _kL=function(_kM,_kN){while(1){if(_kM>=_kJ){if(_kM<=_kJ){if(_kM!=_kJ){return new F(function(){return _kj("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_kN);}}else{return _kN-1|0;}}else{var _kO=imul(_kM,2)>>>0,_kP=_kN+1|0;_kM=_kO;_kN=_kP;continue;}}},_kQ=B(_kL(1,0));return ((_kQ+_kQ|0)!=_kI)?[0,_kI,1]:[0,_kI,0];}}},_kR=function(_kS,_kT){var _kU=E(_kS);if(!_kU[0]){var _kV=_kU[1],_kW=E(_kT);return (_kW[0]==0)?_kV<=_kW[1]:I_compareInt(_kW[1],_kV)>=0;}else{var _kX=_kU[1],_kY=E(_kT);return (_kY[0]==0)?I_compareInt(_kX,_kY[1])<=0:I_compare(_kX,_kY[1])<=0;}},_kZ=function(_l0,_l1){while(1){var _l2=E(_l0);if(!_l2[0]){var _l3=_l2[1],_l4=E(_l1);if(!_l4[0]){return [0,(_l3>>>0&_l4[1]>>>0)>>>0&4294967295];}else{_l0=[1,I_fromInt(_l3)];_l1=_l4;continue;}}else{var _l5=E(_l1);if(!_l5[0]){_l0=_l2;_l1=[1,I_fromInt(_l5[1])];continue;}else{return [1,I_and(_l2[1],_l5[1])];}}}},_l6=function(_l7,_l8){while(1){var _l9=E(_l7);if(!_l9[0]){var _la=_l9[1],_lb=E(_l8);if(!_lb[0]){var _lc=_lb[1],_ld=subC(_la,_lc);if(!E(_ld[2])){return [0,_ld[1]];}else{_l7=[1,I_fromInt(_la)];_l8=[1,I_fromInt(_lc)];continue;}}else{_l7=[1,I_fromInt(_la)];_l8=_lb;continue;}}else{var _le=E(_l8);if(!_le[0]){_l7=_l9;_l8=[1,I_fromInt(_le[1])];continue;}else{return [1,I_sub(_l9[1],_le[1])];}}}},_lf=[0,2],_lg=function(_lh,_li){var _lj=E(_lh);if(!_lj[0]){var _lk=(_lj[1]>>>0&(2<<_li>>>0)-1>>>0)>>>0,_ll=1<<_li>>>0;return (_ll<=_lk)?(_ll>=_lk)?1:2:0;}else{var _lm=B(_kZ(_lj,B(_l6(B(_cz(_lf,_li)),_jn)))),_ln=B(_cz(_jn,_li));return (!B(_jf(_ln,_lm)))?(!B(_fs(_ln,_lm)))?1:2:0;}},_lo=function(_lp,_lq){while(1){var _lr=E(_lp);if(!_lr[0]){_lp=[1,I_fromInt(_lr[1])];continue;}else{return [1,I_shiftRight(_lr[1],_lq)];}}},_ls=function(_lt,_lu,_lv,_lw){var _lx=B(_kz(_lw)),_ly=_lx[1];if(!E(_lx[2])){var _lz=B(_kr(_lv));if(_lz<((_ly+_lt|0)-1|0)){var _lA=_ly+(_lt-_lu|0)|0;if(_lA>0){if(_lA>_lz){if(_lA<=(_lz+1|0)){if(!E(B(_kz(_lv))[2])){return 0;}else{return new F(function(){return _iB(_hO,_lt-_lu|0);});}}else{return 0;}}else{var _lB=B(_lo(_lv,_lA));switch(B(_lg(_lv,_lA-1|0))){case 0:return new F(function(){return _iB(_lB,_lt-_lu|0);});break;case 1:if(!(B(_iN(_lB))&1)){return new F(function(){return _iB(_lB,_lt-_lu|0);});}else{return new F(function(){return _iB(B(_iQ(_lB,_hO)),_lt-_lu|0);});}break;default:return new F(function(){return _iB(B(_iQ(_lB,_hO)),_lt-_lu|0);});}}}else{return new F(function(){return _iB(_lv,(_lt-_lu|0)-_lA|0);});}}else{if(_lz>=_lu){var _lC=B(_lo(_lv,(_lz+1|0)-_lu|0));switch(B(_lg(_lv,_lz-_lu|0))){case 0:return new F(function(){return _iB(_lC,((_lz-_ly|0)+1|0)-_lu|0);});break;case 2:return new F(function(){return _iB(B(_iQ(_lC,_hO)),((_lz-_ly|0)+1|0)-_lu|0);});break;default:if(!(B(_iN(_lC))&1)){return new F(function(){return _iB(_lC,((_lz-_ly|0)+1|0)-_lu|0);});}else{return new F(function(){return _iB(B(_iQ(_lC,_hO)),((_lz-_ly|0)+1|0)-_lu|0);});}}}else{return new F(function(){return _iB(_lv, -_ly);});}}}else{var _lD=B(_kr(_lv))-_ly|0,_lE=function(_lF){var _lG=function(_lH,_lI){if(!B(_kR(B(_cz(_lI,_lu)),_lH))){return new F(function(){return _j9(_lF-_lu|0,_lH,_lI);});}else{return new F(function(){return _j9((_lF-_lu|0)+1|0,_lH,B(_cz(_lI,1)));});}};if(_lF>=_lu){if(_lF!=_lu){return new F(function(){return _lG(_lv,new T(function(){return B(_cz(_lw,_lF-_lu|0));}));});}else{return new F(function(){return _lG(_lv,_lw);});}}else{return new F(function(){return _lG(new T(function(){return B(_cz(_lv,_lu-_lF|0));}),_lw);});}};if(_lt>_lD){return new F(function(){return _lE(_lt);});}else{return new F(function(){return _lE(_lD);});}}},_lJ=[0,2147483647],_lK=new T(function(){return B(_iQ(_lJ,_jn));}),_lL=function(_lM){var _lN=E(_lM);if(!_lN[0]){var _lO=E(_lN[1]);return (_lO==(-2147483648))?E(_lK):[0, -_lO];}else{return [1,I_negate(_lN[1])];}},_lP=new T(function(){return 0/0;}),_lQ=new T(function(){return -1/0;}),_lR=new T(function(){return 1/0;}),_lS=0,_lT=function(_lU,_lV){if(!B(_iF(_lV,_j8))){if(!B(_iF(_lU,_j8))){if(!B(_fs(_lU,_j8))){return new F(function(){return _ls(-1021,53,_lU,_lV);});}else{return  -B(_ls(-1021,53,B(_lL(_lU)),_lV));}}else{return E(_lS);}}else{return (!B(_iF(_lU,_j8)))?(!B(_fs(_lU,_j8)))?E(_lR):E(_lQ):E(_lP);}},_lW=function(_lX){var _lY=E(_lX);return new F(function(){return _lT(_lY[1],_lY[2]);});},_lZ=function(_m0){return 1/E(_m0);},_m1=function(_m2){var _m3=E(_m2),_m4=E(_m3);return (_m4==0)?E(_lS):(_m4<=0)? -_m4:E(_m3);},_m5=function(_m6){return new F(function(){return _bw(_m6);});},_m7=1,_m8=-1,_m9=function(_ma){var _mb=E(_ma);return (_mb<=0)?(_mb>=0)?E(_mb):E(_m8):E(_m7);},_mc=function(_md,_me){return E(_md)-E(_me);},_mf=function(_mg){return  -E(_mg);},_mh=function(_mi,_mj){return E(_mi)+E(_mj);},_mk=function(_ml,_mm){return E(_ml)*E(_mm);},_mn=[0,_mh,_mc,_mk,_mf,_m1,_m9,_m5],_mo=function(_mp,_mq){return E(_mp)/E(_mq);},_mr=[0,_mn,_mo,_lZ,_lW],_ms=function(_mt){return new F(function(){return Math.acos(E(_mt));});},_mu=function(_mv){return new F(function(){return Math.asin(E(_mv));});},_mw=function(_mx){return new F(function(){return Math.atan(E(_mx));});},_my=function(_mz){return new F(function(){return Math.cos(E(_mz));});},_mA=function(_mB){return new F(function(){return cosh(E(_mB));});},_mC=function(_mD){return new F(function(){return Math.exp(E(_mD));});},_mE=function(_mF){return new F(function(){return Math.log(E(_mF));});},_mG=function(_mH,_mI){return new F(function(){return Math.pow(E(_mH),E(_mI));});},_mJ=function(_mK){return new F(function(){return Math.sin(E(_mK));});},_mL=function(_mM){return new F(function(){return sinh(E(_mM));});},_mN=function(_mO){return new F(function(){return Math.sqrt(E(_mO));});},_mP=function(_mQ){return new F(function(){return Math.tan(E(_mQ));});},_mR=function(_mS){return new F(function(){return tanh(E(_mS));});},_mT=[0,_mr,_hN,_mC,_mE,_mN,_mG,_hK,_mJ,_my,_mP,_mu,_ms,_mw,_mL,_mA,_mR,_hE,_hB,_hH],_mU=function(_mV,_mW){if(_mW<=0){var _mX=function(_mY){var _mZ=function(_n0){var _n1=function(_n2){var _n3=function(_n4){var _n5=isDoubleNegativeZero(_mW),_n6=_n5,_n7=function(_n8){var _n9=E(_mV);if(!_n9){return (_mW>=0)?(E(_n6)==0)?E(_mW):3.141592653589793:3.141592653589793;}else{var _na=E(_mW);return (_na==0)?E(_n9):_na+_n9;}};if(!E(_n6)){return new F(function(){return _n7(_);});}else{var _nb=E(_mV),_nc=isDoubleNegativeZero(_nb);if(!E(_nc)){return new F(function(){return _n7(_);});}else{return  -B(_mU( -_nb,_mW));}}};if(_mW>=0){return new F(function(){return _n3(_);});}else{var _nd=E(_mV),_ne=isDoubleNegativeZero(_nd);if(!E(_ne)){return new F(function(){return _n3(_);});}else{return  -B(_mU( -_nd,_mW));}}};if(_mW>0){return new F(function(){return _n1(_);});}else{var _nf=E(_mV);if(_nf>=0){return new F(function(){return _n1(_);});}else{return  -B(_mU( -_nf,_mW));}}};if(_mW>=0){return new F(function(){return _mZ(_);});}else{var _ng=E(_mV);if(_ng<=0){return new F(function(){return _mZ(_);});}else{return 3.141592653589793+Math.atan(_ng/_mW);}}};if(!E(_mW)){if(E(_mV)<=0){return new F(function(){return _mX(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _mX(_);});}}else{return new F(function(){return Math.atan(E(_mV)/_mW);});}},_nh=function(_ni,_nj){return new F(function(){return _mU(_ni,E(_nj));});},_nk=function(_nl){var _nm=B(_bt(E(_nl)));return [0,_nm[1],_nm[2]];},_nn=function(_no,_np){return new F(function(){return _iB(_no,E(_np));});},_nq=function(_nr){var _ns=B(_bt(_nr));return (!B(_iF(_ns[1],_j8)))?_ns[2]+53|0:0;},_nt=function(_nu){return new F(function(){return _nq(E(_nu));});},_nv=53,_nw=function(_nx){return E(_nv);},_ny=[0,2],_nz=function(_nA){return E(_ny);},_nB=1024,_nC=-1021,_nD=[0,_nC,_nB],_nE=function(_nF){return E(_nD);},_nG=function(_nH){var _nI=isDoubleDenormalized(E(_nH));return (E(_nI)==0)?false:true;},_nJ=function(_nK){return true;},_nL=function(_nM){var _nN=isDoubleInfinite(E(_nM));return (E(_nN)==0)?false:true;},_nO=function(_nP){var _nQ=isDoubleNaN(E(_nP));return (E(_nQ)==0)?false:true;},_nR=function(_nS){var _nT=isDoubleNegativeZero(E(_nS));return (E(_nT)==0)?false:true;},_nU=function(_nV,_nW){var _nX=E(_nV);if(!_nX){return E(_nW);}else{var _nY=E(_nW);if(!_nY){return 0;}else{var _nZ=isDoubleFinite(_nY);if(!E(_nZ)){return E(_nY);}else{var _o0=B(_bt(_nY)),_o1=_o0[1],_o2=_o0[2];if(2257>_nX){if(-2257>_nX){return new F(function(){return _iB(_o1,_o2+(-2257)|0);});}else{return new F(function(){return _iB(_o1,_o2+_nX|0);});}}else{return new F(function(){return _iB(_o1,_o2+2257|0);});}}}}},_o3=function(_o4,_o5){return new F(function(){return _nU(E(_o4),E(_o5));});},_o6=function(_o7){return new F(function(){return _iB(B(_bt(E(_o7)))[1],-53);});},_o8=function(_o9,_oa){return (E(_o9)!=E(_oa))?true:false;},_ob=function(_oc,_od){return E(_oc)==E(_od);},_oe=[0,_ob,_o8],_of=function(_og,_oh){return E(_og)<E(_oh);},_oi=function(_oj,_ok){return E(_oj)<=E(_ok);},_ol=function(_om,_on){return E(_om)>E(_on);},_oo=function(_op,_oq){return E(_op)>=E(_oq);},_or=function(_os,_ot){var _ou=E(_os),_ov=E(_ot);return (_ou>=_ov)?(_ou!=_ov)?2:1:0;},_ow=function(_ox,_oy){var _oz=E(_ox),_oA=E(_oy);return (_oz>_oA)?E(_oz):E(_oA);},_oB=function(_oC,_oD){var _oE=E(_oC),_oF=E(_oD);return (_oE>_oF)?E(_oF):E(_oE);},_oG=[0,_oe,_or,_of,_oi,_ol,_oo,_ow,_oB],_oH=new T(function(){var _oI=newByteArr(256),_oJ=_oI,_=_oJ["v"]["i8"][0]=8,_oK=function(_oL,_oM,_oN,_){while(1){if(_oN>=256){if(_oL>=256){return E(_);}else{var _oO=imul(2,_oL)|0,_oP=_oM+1|0,_oQ=_oL;_oL=_oO;_oM=_oP;_oN=_oQ;continue;}}else{var _=_oJ["v"]["i8"][_oN]=_oM,_oQ=_oN+_oL|0;_oN=_oQ;continue;}}},_=B(_oK(2,0,1,_));return _oJ;}),_oR=function(_oS,_oT){while(1){var _oU=B((function(_oV,_oW){var _oX=hs_int64ToInt(_oV),_oY=E(_oH)["v"]["i8"][(255&_oX>>>0)>>>0&4294967295];if(_oW>_oY){if(_oY>=8){var _oZ=hs_uncheckedIShiftRA64(_oV,8),_p0=_oW-8|0;_oS=_oZ;_oT=_p0;return null;}else{return [0,new T(function(){var _p1=hs_uncheckedIShiftRA64(_oV,_oY);return B(_bB(_p1));}),_oW-_oY|0];}}else{return [0,new T(function(){var _p2=hs_uncheckedIShiftRA64(_oV,_oW);return B(_bB(_p2));}),0];}})(_oS,_oT));if(_oU!=null){return _oU;}}},_p3=function(_p4){return I_toInt(_p4)>>>0;},_p5=function(_p6){var _p7=E(_p6);if(!_p7[0]){return _p7[1]>>>0;}else{return new F(function(){return _p3(_p7[1]);});}},_p8=function(_p9){var _pa=B(_bt(_p9)),_pb=_pa[1],_pc=_pa[2];if(_pc<0){var _pd=function(_pe){if(!_pe){return [0,E(_pb),B(_cz(_hO, -_pc))];}else{var _pf=B(_oR(B(_bL(_pb)), -_pc));return [0,E(_pf[1]),B(_cz(_hO,_pf[2]))];}};if(!((B(_p5(_pb))&1)>>>0)){return new F(function(){return _pd(1);});}else{return new F(function(){return _pd(0);});}}else{return [0,B(_cz(_pb,_pc)),_hO];}},_pg=function(_ph){var _pi=B(_p8(E(_ph)));return [0,E(_pi[1]),E(_pi[2])];},_pj=[0,_mn,_oG,_pg],_pk=function(_pl){return E(E(_pl)[1]);},_pm=function(_pn){return E(E(_pn)[1]);},_po=[0,1],_pp=function(_pq,_pr){if(_pq<=_pr){var _ps=function(_pt){return [1,_pt,new T(function(){if(_pt!=_pr){return B(_ps(_pt+1|0));}else{return [0];}})];};return new F(function(){return _ps(_pq);});}else{return [0];}},_pu=function(_pv){return new F(function(){return _pp(E(_pv),2147483647);});},_pw=function(_px,_py,_pz){if(_pz<=_py){var _pA=new T(function(){var _pB=_py-_px|0,_pC=function(_pD){return (_pD>=(_pz-_pB|0))?[1,_pD,new T(function(){return B(_pC(_pD+_pB|0));})]:[1,_pD,_3n];};return B(_pC(_py));});return [1,_px,_pA];}else{return (_pz<=_px)?[1,_px,_3n]:[0];}},_pE=function(_pF,_pG,_pH){if(_pH>=_pG){var _pI=new T(function(){var _pJ=_pG-_pF|0,_pK=function(_pL){return (_pL<=(_pH-_pJ|0))?[1,_pL,new T(function(){return B(_pK(_pL+_pJ|0));})]:[1,_pL,_3n];};return B(_pK(_pG));});return [1,_pF,_pI];}else{return (_pH>=_pF)?[1,_pF,_3n]:[0];}},_pM=function(_pN,_pO){if(_pO<_pN){return new F(function(){return _pw(_pN,_pO,-2147483648);});}else{return new F(function(){return _pE(_pN,_pO,2147483647);});}},_pP=function(_pQ,_pR){return new F(function(){return _pM(E(_pQ),E(_pR));});},_pS=function(_pT,_pU,_pV){if(_pU<_pT){return new F(function(){return _pw(_pT,_pU,_pV);});}else{return new F(function(){return _pE(_pT,_pU,_pV);});}},_pW=function(_pX,_pY,_pZ){return new F(function(){return _pS(E(_pX),E(_pY),E(_pZ));});},_q0=function(_q1,_q2){return new F(function(){return _pp(E(_q1),E(_q2));});},_q3=function(_q4){return E(_q4);},_q5=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_q6=new T(function(){return B(err(_q5));}),_q7=function(_q8){var _q9=E(_q8);return (_q9==(-2147483648))?E(_q6):_q9-1|0;},_qa=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_qb=new T(function(){return B(err(_qa));}),_qc=function(_qd){var _qe=E(_qd);return (_qe==2147483647)?E(_qb):_qe+1|0;},_qf=[0,_qc,_q7,_q3,_q3,_pu,_pP,_q0,_pW],_qg=function(_qh,_qi){if(_qh<=0){if(_qh>=0){return new F(function(){return quot(_qh,_qi);});}else{if(_qi<=0){return new F(function(){return quot(_qh,_qi);});}else{return quot(_qh+1|0,_qi)-1|0;}}}else{if(_qi>=0){if(_qh>=0){return new F(function(){return quot(_qh,_qi);});}else{if(_qi<=0){return new F(function(){return quot(_qh,_qi);});}else{return quot(_qh+1|0,_qi)-1|0;}}}else{return quot(_qh-1|0,_qi)-1|0;}}},_qj=0,_qk=new T(function(){return B(_iw(_qj));}),_ql=new T(function(){return die(_qk);}),_qm=function(_qn,_qo){var _qp=E(_qo);switch(_qp){case -1:var _qq=E(_qn);if(_qq==(-2147483648)){return E(_ql);}else{return new F(function(){return _qg(_qq,-1);});}break;case 0:return E(_iA);default:return new F(function(){return _qg(_qn,_qp);});}},_qr=function(_qs,_qt){return new F(function(){return _qm(E(_qs),E(_qt));});},_qu=0,_qv=[0,_ql,_qu],_qw=function(_qx,_qy){var _qz=E(_qx),_qA=E(_qy);switch(_qA){case -1:var _qB=E(_qz);if(_qB==(-2147483648)){return E(_qv);}else{if(_qB<=0){if(_qB>=0){var _qC=quotRemI(_qB,-1);return [0,_qC[1],_qC[2]];}else{var _qD=quotRemI(_qB,-1);return [0,_qD[1],_qD[2]];}}else{var _qE=quotRemI(_qB-1|0,-1);return [0,_qE[1]-1|0,(_qE[2]+(-1)|0)+1|0];}}break;case 0:return E(_iA);default:if(_qz<=0){if(_qz>=0){var _qF=quotRemI(_qz,_qA);return [0,_qF[1],_qF[2]];}else{if(_qA<=0){var _qG=quotRemI(_qz,_qA);return [0,_qG[1],_qG[2]];}else{var _qH=quotRemI(_qz+1|0,_qA);return [0,_qH[1]-1|0,(_qH[2]+_qA|0)-1|0];}}}else{if(_qA>=0){if(_qz>=0){var _qI=quotRemI(_qz,_qA);return [0,_qI[1],_qI[2]];}else{if(_qA<=0){var _qJ=quotRemI(_qz,_qA);return [0,_qJ[1],_qJ[2]];}else{var _qK=quotRemI(_qz+1|0,_qA);return [0,_qK[1]-1|0,(_qK[2]+_qA|0)-1|0];}}}else{var _qL=quotRemI(_qz-1|0,_qA);return [0,_qL[1]-1|0,(_qL[2]+_qA|0)+1|0];}}}},_qM=function(_qN,_qO){var _qP=_qN%_qO;if(_qN<=0){if(_qN>=0){return E(_qP);}else{if(_qO<=0){return E(_qP);}else{var _qQ=E(_qP);return (_qQ==0)?0:_qQ+_qO|0;}}}else{if(_qO>=0){if(_qN>=0){return E(_qP);}else{if(_qO<=0){return E(_qP);}else{var _qR=E(_qP);return (_qR==0)?0:_qR+_qO|0;}}}else{var _qS=E(_qP);return (_qS==0)?0:_qS+_qO|0;}}},_qT=function(_qU,_qV){var _qW=E(_qV);switch(_qW){case -1:return E(_qu);case 0:return E(_iA);default:return new F(function(){return _qM(E(_qU),_qW);});}},_qX=function(_qY,_qZ){var _r0=E(_qY),_r1=E(_qZ);switch(_r1){case -1:var _r2=E(_r0);if(_r2==(-2147483648)){return E(_ql);}else{return new F(function(){return quot(_r2,-1);});}break;case 0:return E(_iA);default:return new F(function(){return quot(_r0,_r1);});}},_r3=function(_r4,_r5){var _r6=E(_r4),_r7=E(_r5);switch(_r7){case -1:var _r8=E(_r6);if(_r8==(-2147483648)){return E(_qv);}else{var _r9=quotRemI(_r8,-1);return [0,_r9[1],_r9[2]];}break;case 0:return E(_iA);default:var _ra=quotRemI(_r6,_r7);return [0,_ra[1],_ra[2]];}},_rb=function(_rc,_rd){var _re=E(_rd);switch(_re){case -1:return E(_qu);case 0:return E(_iA);default:return E(_rc)%_re;}},_rf=function(_rg){return new F(function(){return _bz(E(_rg));});},_rh=function(_ri){return [0,E(B(_bz(E(_ri)))),E(_po)];},_rj=function(_rk,_rl){return imul(E(_rk),E(_rl))|0;},_rm=function(_rn,_ro){return E(_rn)+E(_ro)|0;},_rp=function(_rq,_rr){return E(_rq)-E(_rr)|0;},_rs=function(_rt){var _ru=E(_rt);return (_ru<0)? -_ru:E(_ru);},_rv=function(_rw){return new F(function(){return _iN(_rw);});},_rx=function(_ry){return  -E(_ry);},_rz=-1,_rA=0,_rB=1,_rC=function(_rD){var _rE=E(_rD);return (_rE>=0)?(E(_rE)==0)?E(_rA):E(_rB):E(_rz);},_rF=[0,_rm,_rp,_rj,_rx,_rs,_rC,_rv],_rG=function(_rH,_rI){return E(_rH)==E(_rI);},_rJ=function(_rK,_rL){return E(_rK)!=E(_rL);},_rM=[0,_rG,_rJ],_rN=function(_rO,_rP){var _rQ=E(_rO),_rR=E(_rP);return (_rQ>_rR)?E(_rQ):E(_rR);},_rS=function(_rT,_rU){var _rV=E(_rT),_rW=E(_rU);return (_rV>_rW)?E(_rW):E(_rV);},_rX=function(_rY,_rZ){return (_rY>=_rZ)?(_rY!=_rZ)?2:1:0;},_s0=function(_s1,_s2){return new F(function(){return _rX(E(_s1),E(_s2));});},_s3=function(_s4,_s5){return E(_s4)>=E(_s5);},_s6=function(_s7,_s8){return E(_s7)>E(_s8);},_s9=function(_sa,_sb){return E(_sa)<=E(_sb);},_sc=function(_sd,_se){return E(_sd)<E(_se);},_sf=[0,_rM,_s0,_sc,_s9,_s6,_s3,_rN,_rS],_sg=[0,_rF,_sf,_rh],_sh=[0,_sg,_qf,_qX,_rb,_qr,_qT,_r3,_qw,_rf],_si=function(_sj,_sk){while(1){var _sl=E(_sj);if(!_sl[0]){var _sm=_sl[1],_sn=E(_sk);if(!_sn[0]){var _so=_sn[1];if(!(imul(_sm,_so)|0)){return [0,imul(_sm,_so)|0];}else{_sj=[1,I_fromInt(_sm)];_sk=[1,I_fromInt(_so)];continue;}}else{_sj=[1,I_fromInt(_sm)];_sk=_sn;continue;}}else{var _sp=E(_sk);if(!_sp[0]){_sj=_sl;_sk=[1,I_fromInt(_sp[1])];continue;}else{return [1,I_mul(_sl[1],_sp[1])];}}}},_sq=function(_sr,_ss,_st){while(1){if(!(_ss%2)){var _su=B(_si(_sr,_sr)),_sv=quot(_ss,2);_sr=_su;_ss=_sv;continue;}else{var _sw=E(_ss);if(_sw==1){return new F(function(){return _si(_sr,_st);});}else{var _su=B(_si(_sr,_sr)),_sx=B(_si(_sr,_st));_sr=_su;_ss=quot(_sw-1|0,2);_st=_sx;continue;}}}},_sy=function(_sz,_sA){while(1){if(!(_sA%2)){var _sB=B(_si(_sz,_sz)),_sC=quot(_sA,2);_sz=_sB;_sA=_sC;continue;}else{var _sD=E(_sA);if(_sD==1){return E(_sz);}else{return new F(function(){return _sq(B(_si(_sz,_sz)),quot(_sD-1|0,2),_sz);});}}}},_sE=function(_sF){return E(E(_sF)[3]);},_sG=function(_sH){return E(E(_sH)[1]);},_sI=function(_sJ){return E(E(_sJ)[2]);},_sK=function(_sL){return E(E(_sL)[2]);},_sM=function(_sN){return E(E(_sN)[3]);},_sO=[0,0],_sP=[0,2],_sQ=function(_sR){return E(E(_sR)[7]);},_sS=function(_sT){return E(E(_sT)[4]);},_sU=function(_sV,_sW){var _sX=B(_pk(_sV)),_sY=new T(function(){return B(_pm(_sX));}),_sZ=new T(function(){return B(A(_sS,[_sV,_sW,new T(function(){return B(A(_sQ,[_sY,_sP]));})]));});return new F(function(){return A(_T,[B(_sG(B(_sI(_sX)))),_sZ,new T(function(){return B(A(_sQ,[_sY,_sO]));})]);});},_t0=new T(function(){return B(unCStr("Negative exponent"));}),_t1=new T(function(){return B(err(_t0));}),_t2=function(_t3){return E(E(_t3)[3]);},_t4=function(_t5,_t6,_t7,_t8){var _t9=B(_pk(_t6)),_ta=new T(function(){return B(_pm(_t9));}),_tb=B(_sI(_t9));if(!B(A(_sM,[_tb,_t8,new T(function(){return B(A(_sQ,[_ta,_sO]));})]))){if(!B(A(_T,[B(_sG(_tb)),_t8,new T(function(){return B(A(_sQ,[_ta,_sO]));})]))){var _tc=new T(function(){return B(A(_sQ,[_ta,_sP]));}),_td=new T(function(){return B(A(_sQ,[_ta,_po]));}),_te=B(_sG(_tb)),_tf=function(_tg,_th,_ti){while(1){var _tj=B((function(_tk,_tl,_tm){if(!B(_sU(_t6,_tl))){if(!B(A(_T,[_te,_tl,_td]))){var _tn=new T(function(){return B(A(_t2,[_t6,new T(function(){return B(A(_sK,[_ta,_tl,_td]));}),_tc]));});_tg=new T(function(){return B(A(_sE,[_t5,_tk,_tk]));});_th=_tn;_ti=new T(function(){return B(A(_sE,[_t5,_tk,_tm]));});return null;}else{return new F(function(){return A(_sE,[_t5,_tk,_tm]);});}}else{var _to=_tm;_tg=new T(function(){return B(A(_sE,[_t5,_tk,_tk]));});_th=new T(function(){return B(A(_t2,[_t6,_tl,_tc]));});_ti=_to;return null;}})(_tg,_th,_ti));if(_tj!=null){return _tj;}}},_tp=_t7,_tq=_t8;while(1){var _tr=B((function(_ts,_tt){if(!B(_sU(_t6,_tt))){if(!B(A(_T,[_te,_tt,_td]))){var _tu=new T(function(){return B(A(_t2,[_t6,new T(function(){return B(A(_sK,[_ta,_tt,_td]));}),_tc]));});return new F(function(){return _tf(new T(function(){return B(A(_sE,[_t5,_ts,_ts]));}),_tu,_ts);});}else{return E(_ts);}}else{_tp=new T(function(){return B(A(_sE,[_t5,_ts,_ts]));});_tq=new T(function(){return B(A(_t2,[_t6,_tt,_tc]));});return null;}})(_tp,_tq));if(_tr!=null){return _tr;}}}else{return new F(function(){return A(_sQ,[_t5,_po]);});}}else{return E(_t1);}},_tv=new T(function(){return B(err(_t0));}),_tw=function(_tx,_ty){var _tz=B(_bt(_ty)),_tA=_tz[1],_tB=_tz[2],_tC=new T(function(){return B(_pm(new T(function(){return B(_pk(_tx));})));});if(_tB<0){var _tD= -_tB;if(_tD>=0){var _tE=E(_tD);if(!_tE){var _tF=E(_po);}else{var _tF=B(_sy(_ny,_tE));}if(!B(_iF(_tF,_j8))){var _tG=B(_iZ(_tA,_tF));return [0,new T(function(){return B(A(_sQ,[_tC,_tG[1]]));}),new T(function(){return B(_iB(_tG[2],_tB));})];}else{return E(_iA);}}else{return E(_tv);}}else{var _tH=new T(function(){var _tI=new T(function(){return B(_t4(_tC,_sh,new T(function(){return B(A(_sQ,[_tC,_ny]));}),_tB));});return B(A(_sE,[_tC,new T(function(){return B(A(_sQ,[_tC,_tA]));}),_tI]));});return [0,_tH,_lS];}},_tJ=function(_tK){return E(E(_tK)[1]);},_tL=function(_tM,_tN){var _tO=B(_tw(_tM,E(_tN))),_tP=_tO[1];if(E(_tO[2])<=0){return E(_tP);}else{var _tQ=B(_pm(B(_pk(_tM))));return new F(function(){return A(_tJ,[_tQ,_tP,new T(function(){return B(A(_sQ,[_tQ,_hO]));})]);});}},_tR=function(_tS,_tT){var _tU=B(_tw(_tS,E(_tT))),_tV=_tU[1];if(E(_tU[2])>=0){return E(_tV);}else{var _tW=B(_pm(B(_pk(_tS))));return new F(function(){return A(_sK,[_tW,_tV,new T(function(){return B(A(_sQ,[_tW,_hO]));})]);});}},_tX=function(_tY,_tZ){var _u0=B(_tw(_tY,E(_tZ)));return [0,_u0[1],_u0[2]];},_u1=function(_u2,_u3){var _u4=B(_tw(_u2,_u3)),_u5=_u4[1],_u6=E(_u4[2]),_u7=new T(function(){var _u8=B(_pm(B(_pk(_u2))));if(_u6>=0){return B(A(_tJ,[_u8,_u5,new T(function(){return B(A(_sQ,[_u8,_hO]));})]));}else{return B(A(_sK,[_u8,_u5,new T(function(){return B(A(_sQ,[_u8,_hO]));})]));}}),_u9=function(_ua){var _ub=_ua-0.5;return (_ub>=0)?(E(_ub)==0)?(!B(_sU(_u2,_u5)))?E(_u7):E(_u5):E(_u7):E(_u5);},_uc=E(_u6);if(!_uc){return new F(function(){return _u9(0);});}else{if(_uc<=0){var _ud= -_uc-0.5;return (_ud>=0)?(E(_ud)==0)?(!B(_sU(_u2,_u5)))?E(_u7):E(_u5):E(_u7):E(_u5);}else{return new F(function(){return _u9(_uc);});}}},_ue=function(_uf,_ug){return new F(function(){return _u1(_uf,E(_ug));});},_uh=function(_ui,_uj){return E(B(_tw(_ui,E(_uj)))[1]);},_uk=[0,_pj,_mr,_tX,_uh,_ue,_tL,_tR],_ul=[0,_uk,_mT,_nz,_nw,_nE,_nk,_nn,_nt,_o6,_o3,_nO,_nL,_nG,_nR,_nJ,_nh],_um=0,_un=1,_uo=2,_up=false,_uq=true,_ur=function(_us){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_7U(9,_us,_3n));}))));});},_ut=1,_uu=function(_uv){return new F(function(){return err(B(unAppCStr("Char.intToDigit: not a digit ",new T(function(){if(_uv>=0){var _uw=jsShowI(_uv);return fromJSStr(_uw);}else{var _ux=jsShowI(_uv);return fromJSStr(_ux);}}))));});},_uy=function(_uz){var _uA=function(_uB){if(_uz<10){return new F(function(){return _uu(_uz);});}else{if(_uz>15){return new F(function(){return _uu(_uz);});}else{return (97+_uz|0)-10|0;}}};if(_uz<0){return new F(function(){return _uA(_);});}else{if(_uz>9){return new F(function(){return _uA(_);});}else{return 48+_uz|0;}}},_uC=function(_uD){return new F(function(){return _uy(E(_uD));});},_uE=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_uF=function(_uG){return new F(function(){return _jV([0,new T(function(){return B(_k8(_uG,_uE));})],_jD);});},_uH=new T(function(){return B(_uF("GHC\\Float.hs:622:11-64|d : ds\'"));}),_uI=0,_uJ=function(_uK,_uL){if(E(_uK)<=0){var _uM=B(_1A(_uC,[1,_uI,_uL]));return (_uM[0]==0)?E(_uH):[0,_uM[1],_uM[2]];}else{var _uN=B(_1A(_uC,_uL));return (_uN[0]==0)?E(_uH):[0,_uN[1],_uN[2]];}},_uO=function(_uP){return E(E(_uP)[1]);},_uQ=function(_uR){return E(E(_uR)[1]);},_uS=function(_uT){return E(E(_uT)[1]);},_uU=function(_uV){return E(E(_uV)[1]);},_uW=function(_uX){return E(E(_uX)[2]);},_uY=46,_uZ=48,_v0=new T(function(){return B(unCStr("0"));}),_v1=function(_v2,_v3,_v4){while(1){var _v5=B((function(_v6,_v7,_v8){var _v9=E(_v6);if(!_v9){var _va=B(_cu(_v7,_3n));if(!_va[0]){return new F(function(){return _16(_v0,[1,_uY,new T(function(){var _vb=E(_v8);if(!_vb[0]){return E(_v0);}else{return E(_vb);}})]);});}else{return new F(function(){return _16(_va,[1,_uY,new T(function(){var _vc=E(_v8);if(!_vc[0]){return E(_v0);}else{return E(_vc);}})]);});}}else{var _vd=E(_v8);if(!_vd[0]){var _ve=[1,_uZ,_v7];_v2=_v9-1|0;_v3=_ve;_v4=_3n;return null;}else{var _ve=[1,_vd[1],_v7];_v2=_v9-1|0;_v3=_ve;_v4=_vd[2];return null;}}})(_v2,_v3,_v4));if(_v5!=null){return _v5;}}},_vf=function(_vg){return new F(function(){return _7U(0,E(_vg),_3n);});},_vh=function(_vi,_vj,_vk){return new F(function(){return _7U(E(_vi),E(_vj),_vk);});},_vl=function(_vm,_vn){return new F(function(){return _7U(0,E(_vm),_vn);});},_vo=function(_vp,_vq){return new F(function(){return _6b(_vl,_vp,_vq);});},_vr=[0,_vh,_vf,_vo],_vs=0,_vt=function(_vu,_vv,_vw){return new F(function(){return A(_vu,[[1,_68,new T(function(){return B(A(_vv,[_vw]));})]]);});},_vx=new T(function(){return B(unCStr("foldr1"));}),_vy=new T(function(){return B(_1q(_vx));}),_vz=function(_vA,_vB){var _vC=E(_vB);if(!_vC[0]){return E(_vy);}else{var _vD=_vC[1],_vE=E(_vC[2]);if(!_vE[0]){return E(_vD);}else{return new F(function(){return A(_vA,[_vD,new T(function(){return B(_vz(_vA,_vE));})]);});}}},_vF=new T(function(){return B(unCStr(" out of range "));}),_vG=new T(function(){return B(unCStr("}.index: Index "));}),_vH=new T(function(){return B(unCStr("Ix{"));}),_vI=[1,_7S,_3n],_vJ=[1,_7S,_vI],_vK=0,_vL=function(_vM){return E(E(_vM)[1]);},_vN=function(_vO,_vP,_vQ,_vR,_vS){var _vT=new T(function(){var _vU=new T(function(){var _vV=new T(function(){var _vW=new T(function(){var _vX=new T(function(){return B(A(_vz,[_vt,[1,new T(function(){return B(A(_vL,[_vQ,_vK,_vR]));}),[1,new T(function(){return B(A(_vL,[_vQ,_vK,_vS]));}),_3n]],_vJ]));});return B(_16(_vF,[1,_7T,[1,_7T,_vX]]));});return B(A(_vL,[_vQ,_vs,_vP,[1,_7S,_vW]]));});return B(_16(_vG,[1,_7T,_vV]));},1);return B(_16(_vO,_vU));},1);return new F(function(){return err(B(_16(_vH,_vT)));});},_vY=function(_vZ,_w0,_w1,_w2,_w3){return new F(function(){return _vN(_vZ,_w0,_w3,_w1,_w2);});},_w4=function(_w5,_w6,_w7,_w8){var _w9=E(_w7);return new F(function(){return _vY(_w5,_w6,_w9[1],_w9[2],_w8);});},_wa=function(_wb,_wc,_wd,_we){return new F(function(){return _w4(_we,_wd,_wc,_wb);});},_wf=new T(function(){return B(unCStr("Int"));}),_wg=function(_wh,_wi,_wj){return new F(function(){return _wa(_vr,[0,_wi,_wj],_wh,_wf);});},_wk=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_wl=new T(function(){return B(err(_wk));}),_wm=1100,_wn=[0,_uI,_wm],_wo=function(_wp){return new F(function(){return _wa(_vr,_wn,_wp,_wf);});},_wq=function(_){var _wr=newArr(1101,_wl),_ws=_wr,_wt=0;while(1){var _wu=B((function(_wv,_){if(0>_wv){return new F(function(){return _wo(_wv);});}else{if(_wv>1100){return new F(function(){return _wo(_wv);});}else{var _=_ws[_wv]=new T(function(){if(_wv>=0){var _ww=E(_wv);if(!_ww){return E(_po);}else{return B(_sy(_ny,_ww));}}else{return E(_tv);}}),_wx=E(_wv);if(_wx==1100){return [0,E(_uI),E(_wm),1101,_ws];}else{_wt=_wx+1|0;return null;}}}})(_wt,_));if(_wu!=null){return _wu;}}},_wy=function(_wz){var _wA=B(A(_wz,[_]));return E(_wA);},_wB=new T(function(){return B(_wy(_wq));}),_wC=[0,10],_wD=324,_wE=[0,_uI,_wD],_wF=function(_wG){return new F(function(){return _wa(_vr,_wE,_wG,_wf);});},_wH=function(_){var _wI=newArr(325,_wl),_wJ=_wI,_wK=0;while(1){var _wL=B((function(_wM,_){if(0>_wM){return new F(function(){return _wF(_wM);});}else{if(_wM>324){return new F(function(){return _wF(_wM);});}else{var _=_wJ[_wM]=new T(function(){if(_wM>=0){var _wN=E(_wM);if(!_wN){return E(_po);}else{return B(_sy(_wC,_wN));}}else{return E(_tv);}}),_wO=E(_wM);if(_wO==324){return [0,E(_uI),E(_wD),325,_wJ];}else{_wK=_wO+1|0;return null;}}}})(_wK,_));if(_wL!=null){return _wL;}}},_wP=new T(function(){return B(_wy(_wH));}),_wQ=function(_wR,_wS){var _wT=function(_wU){if(!B(_iF(_wR,_wC))){if(_wS>=0){var _wV=E(_wS);if(!_wV){return E(_po);}else{return new F(function(){return _sy(_wR,_wV);});}}else{return E(_tv);}}else{if(_wS>324){if(_wS>=0){var _wW=E(_wS);if(!_wW){return E(_po);}else{return new F(function(){return _sy(_wR,_wW);});}}else{return E(_tv);}}else{var _wX=E(_wP),_wY=E(_wX[1]),_wZ=E(_wX[2]);if(_wY>_wS){return new F(function(){return _wg(_wS,_wY,_wZ);});}else{if(_wS>_wZ){return new F(function(){return _wg(_wS,_wY,_wZ);});}else{return E(_wX[4][_wS-_wY|0]);}}}}};if(!B(_iF(_wR,_ny))){return new F(function(){return _wT(_);});}else{if(_wS<0){return new F(function(){return _wT(_);});}else{if(_wS>1100){return new F(function(){return _wT(_);});}else{var _x0=E(_wB),_x1=E(_x0[1]),_x2=E(_x0[2]);if(_x1>_wS){return new F(function(){return _wg(_wS,_x1,_x2);});}else{if(_wS>_x2){return new F(function(){return _wg(_wS,_x1,_x2);});}else{return E(_x0[4][_wS-_x1|0]);}}}}}},_x3=function(_x4){return E(E(_x4)[6]);},_x5=function(_x6){return E(E(_x6)[4]);},_x7=function(_x8){var _x9=E(_x8);if(!_x9[0]){return _x9[1];}else{return new F(function(){return I_toNumber(_x9[1]);});}},_xa=function(_xb){return E(E(_xb)[3]);},_xc=function(_xd){return E(E(_xd)[5]);},_xe=[1,_uI,_3n],_xf=function(_xg,_xh){while(1){var _xi=E(_xg);if(!_xi[0]){var _xj=E(_xi[1]);if(_xj==(-2147483648)){_xg=[1,I_fromInt(-2147483648)];continue;}else{var _xk=E(_xh);if(!_xk[0]){return [0,quot(_xj,_xk[1])];}else{_xg=[1,I_fromInt(_xj)];_xh=_xk;continue;}}}else{var _xl=_xi[1],_xm=E(_xh);return (_xm[0]==0)?[0,I_toInt(I_quot(_xl,I_fromInt(_xm[1])))]:[1,I_quot(_xl,_xm[1])];}}},_xn=function(_xo,_xp,_xq){if(!B(A(_T,[B(_sG(B(_sI(B(_uU(B(_uS(_xo)))))))),_xq,new T(function(){return B(A(_sQ,[B(_uQ(B(_uO(B(_uW(_xo)))))),_j8]));})]))){var _xr=new T(function(){return B(A(_xa,[_xo,_xq]));}),_xs=new T(function(){return B(A(_x5,[_xo,_xq]));}),_xt=new T(function(){return E(B(A(_xc,[_xo,_xq]))[1])-E(_xs)|0;}),_xu=new T(function(){return B(A(_x3,[_xo,_xq]));}),_xv=new T(function(){return E(E(_xu)[2]);}),_xw=new T(function(){var _xx=E(_xv),_xy=E(_xt)-_xx|0;if(_xy<=0){return [0,new T(function(){return E(E(_xu)[1]);}),_xx];}else{return [0,new T(function(){var _xz=B(_wQ(_xr,_xy));if(!B(_iF(_xz,_j8))){return B(_xf(E(_xu)[1],_xz));}else{return E(_iA);}}),_xx+_xy|0];}}),_xA=new T(function(){return E(E(_xw)[2]);}),_xB=new T(function(){return E(E(_xw)[1]);}),_xC=new T(function(){var _xD=E(_xA);if(_xD<0){if(_xD<=E(_xt)){return [0,new T(function(){return B(_si(_xB,_ny));}),new T(function(){return B(_si(B(_wQ(_xr, -_xD)),_ny));}),_hO,_hO];}else{if(!B(_iF(_xB,B(_wQ(_xr,E(_xs)-1|0))))){return [0,new T(function(){return B(_si(_xB,_ny));}),new T(function(){return B(_si(B(_wQ(_xr, -_xD)),_ny));}),_hO,_hO];}else{return [0,new T(function(){return B(_si(B(_si(_xB,_xr)),_ny));}),new T(function(){return B(_si(B(_wQ(_xr, -_xD+1|0)),_ny));}),_xr,_hO];}}}else{var _xE=new T(function(){return B(_wQ(_xr,_xD));});if(!B(_iF(_xB,B(_wQ(_xr,E(_xs)-1|0))))){return [0,new T(function(){return B(_si(B(_si(_xB,_xE)),_ny));}),_ny,_xE,_xE];}else{return [0,new T(function(){return B(_si(B(_si(B(_si(_xB,_xE)),_xr)),_ny));}),new T(function(){return B(_si(_ny,_xr));}),new T(function(){return B(_si(_xE,_xr));}),_xE];}}}),_xF=new T(function(){return E(E(_xC)[2]);}),_xG=new T(function(){return E(E(_xC)[3]);}),_xH=new T(function(){return E(E(_xC)[1]);}),_xI=new T(function(){var _xJ=new T(function(){return B(_iQ(_xH,_xG));}),_xK=function(_xL){var _xM=(Math.log(B(_x7(B(_iQ(_xB,_hO)))))+E(_xA)*Math.log(B(_x7(_xr))))/Math.log(B(_x7(_xp))),_xN=_xM&4294967295;return (_xN>=_xM)?E(_xN):_xN+1|0;},_xO=function(_xP){while(1){if(_xP<0){if(!B(_kR(B(_si(B(_wQ(_xp, -_xP)),_xJ)),_xF))){var _xQ=_xP+1|0;_xP=_xQ;continue;}else{return E(_xP);}}else{if(!B(_kR(_xJ,B(_si(B(_wQ(_xp,_xP)),_xF))))){var _xQ=_xP+1|0;_xP=_xQ;continue;}else{return E(_xP);}}}};if(!B(_iF(_xr,_ny))){return B(_xO(B(_xK(_))));}else{if(!B(_iF(_xp,_wC))){return B(_xO(B(_xK(_))));}else{var _xR=(E(_xs)-1|0)+E(_xv)|0;if(_xR<0){return B(_xO(quot(imul(_xR,8651)|0,28738)));}else{return B(_xO(quot(imul(_xR,8651)|0,28738)+1|0));}}}}),_xS=new T(function(){var _xT=E(_xI),_xU=function(_xV,_xW,_xX,_xY,_xZ){while(1){var _y0=B((function(_y1,_y2,_y3,_y4,_y5){if(!B(_iF(_y3,_j8))){var _y6=B(_iZ(B(_si(_y2,_xp)),_y3)),_y7=_y6[1],_y8=_y6[2],_y9=B(_si(_y5,_xp)),_ya=B(_si(_y4,_xp));if(!B(_fs(_y8,_y9))){if(!B(_jf(B(_iQ(_y8,_ya)),_y3))){var _yb=[1,_y7,_y1],_yc=_y3;_xV=_yb;_xW=_y8;_xX=_yc;_xY=_ya;_xZ=_y9;return null;}else{return [1,new T(function(){return B(_iQ(_y7,_hO));}),_y1];}}else{return (!B(_jf(B(_iQ(_y8,_ya)),_y3)))?[1,_y7,_y1]:(!B(_fs(B(_si(_y8,_ny)),_y3)))?[1,new T(function(){return B(_iQ(_y7,_hO));}),_y1]:[1,_y7,_y1];}}else{return E(_iA);}})(_xV,_xW,_xX,_xY,_xZ));if(_y0!=null){return _y0;}}};if(_xT<0){var _yd=B(_wQ(_xp, -_xT));return B(_1A(_rv,B(_cu(B(_xU(_3n,B(_si(_xH,_yd)),_xF,B(_si(_xG,_yd)),B(_si(E(_xC)[4],_yd)))),_3n))));}else{return B(_1A(_rv,B(_cu(B(_xU(_3n,_xH,B(_si(_xF,B(_wQ(_xp,_xT)))),_xG,E(_xC)[4])),_3n))));}});return [0,_xS,_xI];}else{return [0,_xe,_uI];}},_ye=function(_yf){var _yg=E(_yf);return (_yg==1)?E(_xe):[1,_uI,new T(function(){return B(_ye(_yg-1|0));})];},_yh=function(_yi,_yj){while(1){var _yk=E(_yj);if(!_yk[0]){return true;}else{if(!B(A(_yi,[_yk[1]]))){return false;}else{_yj=_yk[2];continue;}}}},_yl=function(_ym){return (E(_ym)%2==0)?true:false;},_yn=new T(function(){return B(unCStr("roundTo: bad Value"));}),_yo=new T(function(){return B(err(_yn));}),_yp=function(_yq){return (E(_yq)==0)?true:false;},_yr=function(_ys,_yt,_yu){var _yv=new T(function(){return quot(E(_ys),2);}),_yw=function(_yx,_yy,_yz){var _yA=E(_yz);if(!_yA[0]){return [0,_uI,new T(function(){var _yB=E(_yx);if(0>=_yB){return [0];}else{return B(_ye(_yB));}})];}else{var _yC=_yA[1],_yD=_yA[2],_yE=E(_yx);if(!_yE){var _yF=E(_yC),_yG=E(_yv);return (_yF!=_yG)?[0,new T(function(){if(_yF<_yG){return E(_uI);}else{return E(_ut);}}),_3n]:(!E(_yy))?[0,new T(function(){if(_yF<_yG){return E(_uI);}else{return E(_ut);}}),_3n]:(!B(_yh(_yp,_yD)))?[0,new T(function(){if(_yF<_yG){return E(_uI);}else{return E(_ut);}}),_3n]:[0,_uI,_3n];}else{var _yH=B(_yw(_yE-1|0,new T(function(){return B(_yl(_yC));},1),_yD)),_yI=_yH[2],_yJ=E(_yH[1])+E(_yC)|0;return (_yJ!=E(_ys))?[0,_uI,[1,_yJ,_yI]]:[0,_ut,[1,_uI,_yI]];}}},_yK=B(_yw(_yt,_uq,_yu)),_yL=_yK[1],_yM=_yK[2];switch(E(_yL)){case 0:return [0,_yL,_yM];case 1:return [0,_ut,[1,_ut,_yM]];default:return E(_yo);}},_yN=function(_yO,_yP){var _yQ=E(_yP);if(!_yQ[0]){return [0,_3n,_3n];}else{var _yR=_yQ[1],_yS=_yQ[2],_yT=E(_yO);if(_yT==1){return [0,[1,_yR,_3n],_yS];}else{var _yU=new T(function(){var _yV=B(_yN(_yT-1|0,_yS));return [0,_yV[1],_yV[2]];});return [0,[1,_yR,new T(function(){return E(E(_yU)[1]);})],new T(function(){return E(E(_yU)[2]);})];}}},_yW=new T(function(){return B(unCStr("e0"));}),_yX=[1,_uZ,_yW],_yY=function(_yZ){var _z0=E(_yZ);return (_z0==1)?E(_yX):[1,_uZ,new T(function(){return B(_yY(_z0-1|0));})];},_z1=10,_z2=function(_z3,_z4){var _z5=E(_z4);return (_z5[0]==0)?[0]:[1,_z3,new T(function(){return B(_z2(_z5[1],_z5[2]));})];},_z6=new T(function(){return B(unCStr("init"));}),_z7=new T(function(){return B(_1q(_z6));}),_z8=function(_z9){return E(E(_z9)[12]);},_za=function(_zb){return E(E(_zb)[11]);},_zc=function(_zd){return E(E(_zd)[14]);},_ze=new T(function(){return B(unCStr("NaN"));}),_zf=new T(function(){return B(unCStr("-Infinity"));}),_zg=new T(function(){return B(unCStr("formatRealFloat/doFmt/FFExponent: []"));}),_zh=new T(function(){return B(err(_zg));}),_zi=new T(function(){return B(unCStr("Infinity"));}),_zj=[1,_uY,_3n],_zk=101,_zl=new T(function(){return B(_uF("GHC\\Float.hs:594:12-70|(d : ds\')"));}),_zm=new T(function(){return B(unCStr("0.0e0"));}),_zn=function(_zo){return E(E(_zo)[4]);},_zp=45,_zq=function(_zr,_zs,_zt,_zu,_zv){if(!B(A(_za,[_zr,_zv]))){var _zw=new T(function(){return B(_uQ(new T(function(){return B(_uO(new T(function(){return B(_uW(_zr));})));})));});if(!B(A(_z8,[_zr,_zv]))){var _zx=function(_zy,_zz,_zA){while(1){var _zB=B((function(_zC,_zD,_zE){switch(E(_zC)){case 0:var _zF=E(_zt);if(!_zF[0]){var _zG=B(_1A(_uC,_zD));if(!_zG[0]){return E(_zh);}else{var _zH=_zG[2],_zI=E(_zG[1]),_zJ=function(_zK){var _zL=E(_zH);if(!_zL[0]){var _zM=new T(function(){return B(unAppCStr(".0e",new T(function(){return B(_7U(0,E(_zE)-1|0,_3n));})));});return [1,_zI,_zM];}else{var _zN=new T(function(){var _zO=new T(function(){return B(unAppCStr("e",new T(function(){return B(_7U(0,E(_zE)-1|0,_3n));})));},1);return B(_16(_zL,_zO));});return [1,_zI,[1,_uY,_zN]];}};if(E(_zI)==48){if(!E(_zH)[0]){return E(_zm);}else{return new F(function(){return _zJ(_);});}}else{return new F(function(){return _zJ(_);});}}}else{var _zP=new T(function(){var _zQ=E(_zF[1]);if(_zQ>1){return E(_zQ);}else{return E(_ut);}}),_zR=function(_zS){var _zT=new T(function(){var _zU=B(_yr(_z1,new T(function(){return E(_zP)+1|0;},1),_zD));return [0,_zU[1],_zU[2]];}),_zV=new T(function(){return E(E(_zT)[1]);}),_zW=new T(function(){if(E(_zV)<=0){var _zX=B(_1A(_uC,E(_zT)[2]));if(!_zX[0]){return E(_zl);}else{return [0,_zX[1],_zX[2]];}}else{var _zY=E(E(_zT)[2]);if(!_zY[0]){return E(_z7);}else{var _zZ=B(_1A(_uC,B(_z2(_zY[1],_zY[2]))));if(!_zZ[0]){return E(_zl);}else{return [0,_zZ[1],_zZ[2]];}}}}),_A0=new T(function(){return B(_16(E(_zW)[2],[1,_zk,new T(function(){return B(_7U(0,(E(_zE)-1|0)+E(_zV)|0,_3n));})]));});return [1,new T(function(){return E(E(_zW)[1]);}),[1,_uY,_A0]];},_A1=E(_zD);if(!_A1[0]){return new F(function(){return _zR(_);});}else{if(!E(_A1[1])){if(!E(_A1[2])[0]){return [1,_uZ,[1,_uY,new T(function(){var _A2=E(_zP);if(0>=_A2){return E(_yW);}else{return B(_yY(_A2));}})]];}else{return new F(function(){return _zR(_);});}}else{return new F(function(){return _zR(_);});}}}break;case 1:var _A3=E(_zt);if(!_A3[0]){var _A4=E(_zE);if(_A4>0){return new F(function(){return _v1(_A4,_3n,new T(function(){return B(_1A(_uC,_zD));},1));});}else{var _A5=new T(function(){var _A6= -_A4;if(0>=_A6){return B(_1A(_uC,_zD));}else{var _A7=new T(function(){return B(_1A(_uC,_zD));}),_A8=function(_A9){var _Aa=E(_A9);return (_Aa==1)?[1,_uZ,_A7]:[1,_uZ,new T(function(){return B(_A8(_Aa-1|0));})];};return B(_A8(_A6));}});return new F(function(){return unAppCStr("0.",_A5);});}}else{var _Ab=_A3[1],_Ac=E(_zE);if(_Ac<0){var _Ad=new T(function(){var _Ae= -_Ac;if(0>=_Ae){var _Af=B(_yr(_z1,new T(function(){var _Ag=E(_Ab);if(_Ag>0){return E(_Ag);}else{return E(_uI);}},1),_zD));return B(_uJ(_Af[1],_Af[2]));}else{var _Ah=function(_Ai){var _Aj=E(_Ai);return (_Aj==1)?[1,_uI,_zD]:[1,_uI,new T(function(){return B(_Ah(_Aj-1|0));})];},_Ak=B(_yr(_z1,new T(function(){var _Al=E(_Ab);if(_Al>0){return E(_Al);}else{return E(_uI);}},1),B(_Ah(_Ae))));return B(_uJ(_Ak[1],_Ak[2]));}});return [1,new T(function(){return E(E(_Ad)[1]);}),new T(function(){var _Am=E(E(_Ad)[2]);if(!_Am[0]){if(!E(_zu)){return [0];}else{return E(_zj);}}else{return [1,_uY,_Am];}})];}else{var _An=B(_yr(_z1,new T(function(){var _Ao=E(_Ab);if(_Ao>0){return _Ao+_Ac|0;}else{return E(_Ac);}},1),_zD)),_Ap=_An[2],_Aq=_Ac+E(_An[1])|0;if(_Aq>0){var _Ar=B(_yN(_Aq,B(_1A(_uC,_Ap)))),_As=_Ar[2],_At=E(_Ar[1]);if(!_At[0]){return new F(function(){return _16(_v0,new T(function(){var _Au=E(_As);if(!_Au[0]){if(!E(_zu)){return [0];}else{return E(_zj);}}else{return [1,_uY,_Au];}},1));});}else{return new F(function(){return _16(_At,new T(function(){var _Av=E(_As);if(!_Av[0]){if(!E(_zu)){return [0];}else{return E(_zj);}}else{return [1,_uY,_Av];}},1));});}}else{return new F(function(){return _16(_v0,new T(function(){var _Aw=B(_1A(_uC,_Ap));if(!_Aw[0]){if(!E(_zu)){return [0];}else{return E(_zj);}}else{return [1,_uY,_Aw];}},1));});}}}break;default:var _Ax=E(_zE);if(_Ax>=0){if(_Ax<=7){var _Ay=_zD;_zy=_un;_zz=_Ay;_zA=_Ax;return null;}else{var _Ay=_zD;_zy=_um;_zz=_Ay;_zA=_Ax;return null;}}else{var _Ay=_zD;_zy=_um;_zz=_Ay;_zA=_Ax;return null;}}})(_zy,_zz,_zA));if(_zB!=null){return _zB;}}},_Az=function(_AA){var _AB=new T(function(){var _AC=B(_xn(_zr,_wC,new T(function(){return B(A(_zn,[_zw,_zv]));})));return B(_zx(_zs,_AC[1],_AC[2]));});return [1,_zp,_AB];};if(!B(A(_sM,[B(_sI(B(_uU(B(_uS(_zr)))))),_zv,new T(function(){return B(A(_sQ,[_zw,_j8]));})]))){if(!B(A(_zc,[_zr,_zv]))){var _AD=B(_xn(_zr,_wC,_zv));return new F(function(){return _zx(_zs,_AD[1],_AD[2]);});}else{return new F(function(){return _Az(_);});}}else{return new F(function(){return _Az(_);});}}else{return (!B(A(_sM,[B(_sI(B(_uU(B(_uS(_zr)))))),_zv,new T(function(){return B(A(_sQ,[_zw,_j8]));})])))?E(_zi):E(_zf);}}else{return E(_ze);}},_AE=function(_AF){var _AG=u_towupper(E(_AF));if(_AG>>>0>1114111){return new F(function(){return _ur(_AG);});}else{return _AG;}},_AH=function(_AI,_AJ,_AK,_AL){var _AM=u_iswupper(_AI),_AN=_AM,_AO=u_towlower(_AI);if(_AO>>>0>1114111){var _AP=B(_ur(_AO));}else{switch(_AO){case 101:var _AQ=B(_zq(_ul,_um,_AJ,_up,_AL));break;case 102:if(!E(_AK)){var _AR=B(_zq(_ul,_un,_AJ,_up,_AL));}else{var _AR=B(_zq(_ul,_un,_AJ,_uq,_AL));}var _AQ=_AR;break;case 103:if(!E(_AK)){var _AS=B(_zq(_ul,_uo,_AJ,_up,_AL));}else{var _AS=B(_zq(_ul,_uo,_AJ,_uq,_AL));}var _AQ=_AS;break;default:var _AQ=E(_hA);}var _AP=_AQ;}if(!E(_AN)){var _AT=E(_AP);return (_AT[0]==0)?[0,_3n,_3n]:(E(_AT[1])==45)?[0,_hy,_AT[2]]:[0,_3n,_AT];}else{var _AU=B(_1A(_AE,_AP));return (_AU[0]==0)?[0,_3n,_3n]:(E(_AU[1])==45)?[0,_hy,_AU[2]]:[0,_3n,_AU];}},_AV=new T(function(){return B(unCStr(" "));}),_AW=new T(function(){return B(unCStr("+"));}),_AX=48,_AY=32,_AZ=function(_B0,_B1){while(1){var _B2=E(_B0);if(!_B2[0]){return E(_B1);}else{var _B3=_B1+1|0;_B0=_B2[2];_B1=_B3;continue;}}},_B4=function(_B5,_B6,_B7,_B8){var _B9=new T(function(){var _Ba=E(_B6);if(!_Ba[0]){return false;}else{if(!E(_Ba[1])){return false;}else{return true;}}}),_Bb=new T(function(){var _Bc=E(_B5);if(!_Bc[0]){return [0];}else{var _Bd=E(_Bc[1]),_Be=B(_AZ(_B7,0))+B(_AZ(_B8,0))|0;if(_Be>=_Bd){return [0];}else{var _Bf=_Bd-_Be|0;if(0>=_Bf){return [0];}else{var _Bg=new T(function(){if(!E(_B9)){return E(_AY);}else{return E(_AX);}}),_Bh=function(_Bi){var _Bj=E(_Bi);return (_Bj==1)?[1,_Bg,_3n]:[1,_Bg,new T(function(){return B(_Bh(_Bj-1|0));})];};return B(_Bh(_Bf));}}}}),_Bk=function(_Bl){if(!E(_B9)){return new F(function(){return _16(_Bb,new T(function(){return B(_16(_B7,_B8));},1));});}else{return new F(function(){return _16(_B7,new T(function(){return B(_16(_Bb,_B8));},1));});}},_Bm=E(_B6);if(!_Bm[0]){return new F(function(){return _Bk(_);});}else{if(!E(_Bm[1])){return new F(function(){return _16(_B7,new T(function(){return B(_16(_B8,_Bb));},1));});}else{return new F(function(){return _Bk(_);});}}},_Bn=function(_Bo,_Bp,_Bq,_Br,_Bs){var _Bt=E(_Bq);if(!_Bt[0]){return new F(function(){return _B4(_Bo,_Bp,_Br,_Bs);});}else{if(!E(_Bt[1])){var _Bu=E(_Br);if(!_Bu[0]){return new F(function(){return _B4(_Bo,_Bp,_AW,_Bs);});}else{return new F(function(){return _B4(_Bo,_Bp,_Bu,_Bs);});}}else{var _Bv=E(_Br);if(!_Bv[0]){return new F(function(){return _B4(_Bo,_Bp,_AV,_Bs);});}else{return new F(function(){return _B4(_Bo,_Bp,_Bv,_Bs);});}}}},_Bw=function(_Bx,_By,_Bz,_BA,_BB,_BC,_BD){var _BE=E(_BD);switch(_BE){case 69:var _BF=new T(function(){var _BG=B(_AH(69,_Bz,_BC,_Bx));return B(_Bn(_By,_BA,_BB,_BG[1],_BG[2]));});return function(_BH){return new F(function(){return _16(_BF,_BH);});};case 70:var _BI=new T(function(){var _BJ=B(_AH(70,_Bz,_BC,_Bx));return B(_Bn(_By,_BA,_BB,_BJ[1],_BJ[2]));});return function(_BH){return new F(function(){return _16(_BI,_BH);});};case 71:var _BK=new T(function(){var _BL=B(_AH(71,_Bz,_BC,_Bx));return B(_Bn(_By,_BA,_BB,_BL[1],_BL[2]));});return function(_BH){return new F(function(){return _16(_BK,_BH);});};case 101:var _BM=new T(function(){var _BN=B(_AH(101,_Bz,_BC,_Bx));return B(_Bn(_By,_BA,_BB,_BN[1],_BN[2]));});return function(_BH){return new F(function(){return _16(_BM,_BH);});};case 102:var _BO=new T(function(){var _BP=B(_AH(102,_Bz,_BC,_Bx));return B(_Bn(_By,_BA,_BB,_BP[1],_BP[2]));});return function(_BH){return new F(function(){return _16(_BO,_BH);});};case 103:var _BQ=new T(function(){var _BR=B(_AH(103,_Bz,_BC,_Bx));return B(_Bn(_By,_BA,_BB,_BR[1],_BR[2]));});return function(_BH){return new F(function(){return _16(_BQ,_BH);});};case 118:var _BS=new T(function(){var _BT=B(_AH(103,_Bz,_BC,_Bx));return B(_Bn(_By,_BA,_BB,_BT[1],_BT[2]));});return function(_BH){return new F(function(){return _16(_BS,_BH);});};default:return new F(function(){return _ht(_BE);});}},_BU=function(_BV,_BW){var _BX=E(_BW);return new F(function(){return _Bw(_BV,_BX[1],_BX[2],_BX[3],_BX[4],_BX[5],E(_BX[7]));});},_BY=function(_BZ){return E(_BZ);},_C0=new T(function(){return B(unCStr("printf: argument list ended prematurely"));}),_C1=new T(function(){return B(err(_C0));}),_C2=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_C3=new T(function(){return B(err(_C2));}),_C4=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_C5=new T(function(){return B(err(_C4));}),_C6=new T(function(){return B(_kj("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_C7=function(_C8,_C9){while(1){var _Ca=B((function(_Cb,_Cc){var _Cd=E(_Cb);switch(_Cd[0]){case 0:var _Ce=E(_Cc);if(!_Ce[0]){return [0];}else{_C8=B(A(_Cd[1],[_Ce[1]]));_C9=_Ce[2];return null;}break;case 1:var _Cf=B(A(_Cd[1],[_Cc])),_Cg=_Cc;_C8=_Cf;_C9=_Cg;return null;case 2:return [0];case 3:return [1,[0,_Cd[1],_Cc],new T(function(){return B(_C7(_Cd[2],_Cc));})];default:return E(_Cd[1]);}})(_C8,_C9));if(_Ca!=null){return _Ca;}}},_Ch=function(_Ci,_Cj){var _Ck=function(_Cl){var _Cm=E(_Cj);if(_Cm[0]==3){return [3,_Cm[1],new T(function(){return B(_Ch(_Ci,_Cm[2]));})];}else{var _Cn=E(_Ci);if(_Cn[0]==2){return E(_Cm);}else{var _Co=E(_Cm);if(_Co[0]==2){return E(_Cn);}else{var _Cp=function(_Cq){var _Cr=E(_Co);if(_Cr[0]==4){return [1,function(_Cs){return [4,new T(function(){return B(_16(B(_C7(_Cn,_Cs)),_Cr[1]));})];}];}else{var _Ct=E(_Cn);if(_Ct[0]==1){var _Cu=_Ct[1],_Cv=E(_Cr);if(!_Cv[0]){return [1,function(_Cw){return new F(function(){return _Ch(B(A(_Cu,[_Cw])),_Cv);});}];}else{return [1,function(_Cx){return new F(function(){return _Ch(B(A(_Cu,[_Cx])),new T(function(){return B(A(_Cv[1],[_Cx]));}));});}];}}else{var _Cy=E(_Cr);if(!_Cy[0]){return E(_C6);}else{return [1,function(_Cz){return new F(function(){return _Ch(_Ct,new T(function(){return B(A(_Cy[1],[_Cz]));}));});}];}}}},_CA=E(_Cn);switch(_CA[0]){case 1:var _CB=E(_Co);if(_CB[0]==4){return [1,function(_CC){return [4,new T(function(){return B(_16(B(_C7(B(A(_CA[1],[_CC])),_CC)),_CB[1]));})];}];}else{return new F(function(){return _Cp(_);});}break;case 4:var _CD=_CA[1],_CE=E(_Co);switch(_CE[0]){case 0:return [1,function(_CF){return [4,new T(function(){return B(_16(_CD,new T(function(){return B(_C7(_CE,_CF));},1)));})];}];case 1:return [1,function(_CG){return [4,new T(function(){return B(_16(_CD,new T(function(){return B(_C7(B(A(_CE[1],[_CG])),_CG));},1)));})];}];default:return [4,new T(function(){return B(_16(_CD,_CE[1]));})];}break;default:return new F(function(){return _Cp(_);});}}}}},_CH=E(_Ci);switch(_CH[0]){case 0:var _CI=E(_Cj);if(!_CI[0]){return [0,function(_CJ){return new F(function(){return _Ch(B(A(_CH[1],[_CJ])),new T(function(){return B(A(_CI[1],[_CJ]));}));});}];}else{return new F(function(){return _Ck(_);});}break;case 3:return [3,_CH[1],new T(function(){return B(_Ch(_CH[2],_Cj));})];default:return new F(function(){return _Ck(_);});}},_CK=new T(function(){return B(unCStr("("));}),_CL=new T(function(){return B(unCStr(")"));}),_CM=function(_CN,_CO){while(1){var _CP=E(_CN);if(!_CP[0]){return (E(_CO)[0]==0)?true:false;}else{var _CQ=E(_CO);if(!_CQ[0]){return false;}else{if(E(_CP[1])!=E(_CQ[1])){return false;}else{_CN=_CP[2];_CO=_CQ[2];continue;}}}}},_CR=function(_CS,_CT){return (!B(_CM(_CS,_CT)))?true:false;},_CU=[0,_CM,_CR],_CV=function(_CW,_CX){var _CY=E(_CW);switch(_CY[0]){case 0:return [0,function(_CZ){return new F(function(){return _CV(B(A(_CY[1],[_CZ])),_CX);});}];case 1:return [1,function(_D0){return new F(function(){return _CV(B(A(_CY[1],[_D0])),_CX);});}];case 2:return [2];case 3:return new F(function(){return _Ch(B(A(_CX,[_CY[1]])),new T(function(){return B(_CV(_CY[2],_CX));}));});break;default:var _D1=function(_D2){var _D3=E(_D2);if(!_D3[0]){return [0];}else{var _D4=E(_D3[1]);return new F(function(){return _16(B(_C7(B(A(_CX,[_D4[1]])),_D4[2])),new T(function(){return B(_D1(_D3[2]));},1));});}},_D5=B(_D1(_CY[1]));return (_D5[0]==0)?[2]:[4,_D5];}},_D6=[2],_D7=function(_D8){return [3,_D8,_D6];},_D9=function(_Da,_Db){var _Dc=E(_Da);if(!_Dc){return new F(function(){return A(_Db,[_a]);});}else{var _Dd=new T(function(){return B(_D9(_Dc-1|0,_Db));});return [0,function(_De){return E(_Dd);}];}},_Df=function(_Dg,_Dh,_Di){var _Dj=new T(function(){return B(A(_Dg,[_D7]));}),_Dk=function(_Dl,_Dm,_Dn,_Do){while(1){var _Dp=B((function(_Dq,_Dr,_Ds,_Dt){var _Du=E(_Dq);switch(_Du[0]){case 0:var _Dv=E(_Dr);if(!_Dv[0]){return new F(function(){return A(_Dh,[_Dt]);});}else{var _Dw=_Ds+1|0,_Dx=_Dt;_Dl=B(A(_Du[1],[_Dv[1]]));_Dm=_Dv[2];_Dn=_Dw;_Do=_Dx;return null;}break;case 1:var _Dy=B(A(_Du[1],[_Dr])),_Dz=_Dr,_Dw=_Ds,_Dx=_Dt;_Dl=_Dy;_Dm=_Dz;_Dn=_Dw;_Do=_Dx;return null;case 2:return new F(function(){return A(_Dh,[_Dt]);});break;case 3:var _DA=new T(function(){return B(_CV(_Du,_Dt));});return new F(function(){return _D9(_Ds,function(_DB){return E(_DA);});});break;default:return new F(function(){return _CV(_Du,_Dt);});}})(_Dl,_Dm,_Dn,_Do));if(_Dp!=null){return _Dp;}}};return function(_DC){return new F(function(){return _Dk(_Dj,_DC,0,_Di);});};},_DD=function(_DE){return new F(function(){return A(_DE,[_3n]);});},_DF=function(_DG,_DH){var _DI=function(_DJ){var _DK=E(_DJ);if(!_DK[0]){return E(_DD);}else{var _DL=_DK[1];if(!B(A(_DG,[_DL]))){return E(_DD);}else{var _DM=new T(function(){return B(_DI(_DK[2]));}),_DN=function(_DO){var _DP=new T(function(){return B(A(_DM,[function(_DQ){return new F(function(){return A(_DO,[[1,_DL,_DQ]]);});}]));});return [0,function(_DR){return E(_DP);}];};return E(_DN);}}};return function(_DS){return new F(function(){return A(_DI,[_DS,_DH]);});};},_DT=[6],_DU=new T(function(){return B(unCStr("valDig: Bad base"));}),_DV=new T(function(){return B(err(_DU));}),_DW=function(_DX,_DY){var _DZ=function(_E0,_E1){var _E2=E(_E0);if(!_E2[0]){var _E3=new T(function(){return B(A(_E1,[_3n]));});return function(_E4){return new F(function(){return A(_E4,[_E3]);});};}else{var _E5=E(_E2[1]),_E6=function(_E7){var _E8=new T(function(){return B(_DZ(_E2[2],function(_E9){return new F(function(){return A(_E1,[[1,_E7,_E9]]);});}));}),_Ea=function(_Eb){var _Ec=new T(function(){return B(A(_E8,[_Eb]));});return [0,function(_Ed){return E(_Ec);}];};return E(_Ea);};switch(E(_DX)){case 8:if(48>_E5){var _Ee=new T(function(){return B(A(_E1,[_3n]));});return function(_Ef){return new F(function(){return A(_Ef,[_Ee]);});};}else{if(_E5>55){var _Eg=new T(function(){return B(A(_E1,[_3n]));});return function(_Eh){return new F(function(){return A(_Eh,[_Eg]);});};}else{return new F(function(){return _E6(_E5-48|0);});}}break;case 10:if(48>_E5){var _Ei=new T(function(){return B(A(_E1,[_3n]));});return function(_Ej){return new F(function(){return A(_Ej,[_Ei]);});};}else{if(_E5>57){var _Ek=new T(function(){return B(A(_E1,[_3n]));});return function(_El){return new F(function(){return A(_El,[_Ek]);});};}else{return new F(function(){return _E6(_E5-48|0);});}}break;case 16:if(48>_E5){if(97>_E5){if(65>_E5){var _Em=new T(function(){return B(A(_E1,[_3n]));});return function(_En){return new F(function(){return A(_En,[_Em]);});};}else{if(_E5>70){var _Eo=new T(function(){return B(A(_E1,[_3n]));});return function(_Ep){return new F(function(){return A(_Ep,[_Eo]);});};}else{return new F(function(){return _E6((_E5-65|0)+10|0);});}}}else{if(_E5>102){if(65>_E5){var _Eq=new T(function(){return B(A(_E1,[_3n]));});return function(_Er){return new F(function(){return A(_Er,[_Eq]);});};}else{if(_E5>70){var _Es=new T(function(){return B(A(_E1,[_3n]));});return function(_Et){return new F(function(){return A(_Et,[_Es]);});};}else{return new F(function(){return _E6((_E5-65|0)+10|0);});}}}else{return new F(function(){return _E6((_E5-97|0)+10|0);});}}}else{if(_E5>57){if(97>_E5){if(65>_E5){var _Eu=new T(function(){return B(A(_E1,[_3n]));});return function(_Ev){return new F(function(){return A(_Ev,[_Eu]);});};}else{if(_E5>70){var _Ew=new T(function(){return B(A(_E1,[_3n]));});return function(_Ex){return new F(function(){return A(_Ex,[_Ew]);});};}else{return new F(function(){return _E6((_E5-65|0)+10|0);});}}}else{if(_E5>102){if(65>_E5){var _Ey=new T(function(){return B(A(_E1,[_3n]));});return function(_Ez){return new F(function(){return A(_Ez,[_Ey]);});};}else{if(_E5>70){var _EA=new T(function(){return B(A(_E1,[_3n]));});return function(_EB){return new F(function(){return A(_EB,[_EA]);});};}else{return new F(function(){return _E6((_E5-65|0)+10|0);});}}}else{return new F(function(){return _E6((_E5-97|0)+10|0);});}}}else{return new F(function(){return _E6(_E5-48|0);});}}break;default:return E(_DV);}}},_EC=function(_ED){var _EE=E(_ED);if(!_EE[0]){return [2];}else{return new F(function(){return A(_DY,[_EE]);});}};return function(_EF){return new F(function(){return A(_DZ,[_EF,_Q,_EC]);});};},_EG=16,_EH=8,_EI=function(_EJ){var _EK=function(_EL){return new F(function(){return A(_EJ,[[5,[0,_EH,_EL]]]);});},_EM=function(_EN){return new F(function(){return A(_EJ,[[5,[0,_EG,_EN]]]);});},_EO=function(_EP){switch(E(_EP)){case 79:return [1,B(_DW(_EH,_EK))];case 88:return [1,B(_DW(_EG,_EM))];case 111:return [1,B(_DW(_EH,_EK))];case 120:return [1,B(_DW(_EG,_EM))];default:return [2];}};return function(_EQ){return (E(_EQ)==48)?[0,_EO]:[2];};},_ER=function(_ES){return [0,B(_EI(_ES))];},_ET=function(_EU){return new F(function(){return A(_EU,[_6t]);});},_EV=function(_EW){return new F(function(){return A(_EW,[_6t]);});},_EX=10,_EY=[0,10],_EZ=function(_F0){return new F(function(){return _bz(E(_F0));});},_F1=new T(function(){return B(unCStr("this should not happen"));}),_F2=new T(function(){return B(err(_F1));}),_F3=function(_F4,_F5){var _F6=E(_F5);if(!_F6[0]){return [0];}else{var _F7=E(_F6[2]);return (_F7[0]==0)?E(_F2):[1,B(_iQ(B(_si(_F6[1],_F4)),_F7[1])),new T(function(){return B(_F3(_F4,_F7[2]));})];}},_F8=[0,0],_F9=function(_Fa,_Fb,_Fc){while(1){var _Fd=B((function(_Fe,_Ff,_Fg){var _Fh=E(_Fg);if(!_Fh[0]){return E(_F8);}else{if(!E(_Fh[2])[0]){return E(_Fh[1]);}else{var _Fi=E(_Ff);if(_Fi<=40){var _Fj=_F8,_Fk=_Fh;while(1){var _Fl=E(_Fk);if(!_Fl[0]){return E(_Fj);}else{var _Fm=B(_iQ(B(_si(_Fj,_Fe)),_Fl[1]));_Fj=_Fm;_Fk=_Fl[2];continue;}}}else{var _Fn=B(_si(_Fe,_Fe));if(!(_Fi%2)){var _Fo=B(_F3(_Fe,_Fh));_Fa=_Fn;_Fb=quot(_Fi+1|0,2);_Fc=_Fo;return null;}else{var _Fo=B(_F3(_Fe,[1,_F8,_Fh]));_Fa=_Fn;_Fb=quot(_Fi+1|0,2);_Fc=_Fo;return null;}}}}})(_Fa,_Fb,_Fc));if(_Fd!=null){return _Fd;}}},_Fp=function(_Fq,_Fr){return new F(function(){return _F9(_Fq,new T(function(){return B(_AZ(_Fr,0));},1),B(_1A(_EZ,_Fr)));});},_Fs=function(_Ft){var _Fu=new T(function(){var _Fv=new T(function(){var _Fw=function(_Fx){return new F(function(){return A(_Ft,[[1,new T(function(){return B(_Fp(_EY,_Fx));})]]);});};return [1,B(_DW(_EX,_Fw))];}),_Fy=function(_Fz){if(E(_Fz)==43){var _FA=function(_FB){return new F(function(){return A(_Ft,[[1,new T(function(){return B(_Fp(_EY,_FB));})]]);});};return [1,B(_DW(_EX,_FA))];}else{return [2];}},_FC=function(_FD){if(E(_FD)==45){var _FE=function(_FF){return new F(function(){return A(_Ft,[[1,new T(function(){return B(_lL(B(_Fp(_EY,_FF))));})]]);});};return [1,B(_DW(_EX,_FE))];}else{return [2];}};return B(_Ch(B(_Ch([0,_FC],[0,_Fy])),_Fv));});return new F(function(){return _Ch([0,function(_FG){return (E(_FG)==101)?E(_Fu):[2];}],[0,function(_FH){return (E(_FH)==69)?E(_Fu):[2];}]);});},_FI=function(_FJ){var _FK=function(_FL){return new F(function(){return A(_FJ,[[1,_FL]]);});};return function(_FM){return (E(_FM)==46)?[1,B(_DW(_EX,_FK))]:[2];};},_FN=function(_FO){return [0,B(_FI(_FO))];},_FP=function(_FQ){var _FR=function(_FS){var _FT=function(_FU){return [1,B(_Df(_Fs,_ET,function(_FV){return new F(function(){return A(_FQ,[[5,[1,_FS,_FU,_FV]]]);});}))];};return [1,B(_Df(_FN,_EV,_FT))];};return new F(function(){return _DW(_EX,_FR);});},_FW=function(_FX){return [1,B(_FP(_FX))];},_FY=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_FZ=function(_G0){return new F(function(){return _f5(_f4,_G0,_FY);});},_G1=function(_G2){var _G3=new T(function(){return B(A(_G2,[_EH]));}),_G4=new T(function(){return B(A(_G2,[_EG]));});return function(_G5){switch(E(_G5)){case 79:return E(_G3);case 88:return E(_G4);case 111:return E(_G3);case 120:return E(_G4);default:return [2];}};},_G6=function(_G7){return [0,B(_G1(_G7))];},_G8=function(_G9){return new F(function(){return A(_G9,[_EX]);});},_Ga=function(_Gb){return [2];},_Gc=function(_Gd){var _Ge=E(_Gd);if(!_Ge[0]){return E(_Ga);}else{var _Gf=_Ge[1],_Gg=E(_Ge[2]);if(!_Gg[0]){return E(_Gf);}else{var _Gh=new T(function(){return B(_Gc(_Gg));}),_Gi=function(_Gj){return new F(function(){return _Ch(B(A(_Gf,[_Gj])),new T(function(){return B(A(_Gh,[_Gj]));}));});};return E(_Gi);}}},_Gk=function(_Gl,_Gm){var _Gn=function(_Go,_Gp,_Gq){var _Gr=E(_Go);if(!_Gr[0]){return new F(function(){return A(_Gq,[_Gl]);});}else{var _Gs=E(_Gp);if(!_Gs[0]){return [2];}else{if(E(_Gr[1])!=E(_Gs[1])){return [2];}else{var _Gt=new T(function(){return B(_Gn(_Gr[2],_Gs[2],_Gq));});return [0,function(_Gu){return E(_Gt);}];}}}};return function(_Gv){return new F(function(){return _Gn(_Gl,_Gv,_Gm);});};},_Gw=new T(function(){return B(unCStr("SO"));}),_Gx=14,_Gy=function(_Gz){var _GA=new T(function(){return B(A(_Gz,[_Gx]));});return [1,B(_Gk(_Gw,function(_GB){return E(_GA);}))];},_GC=new T(function(){return B(unCStr("SOH"));}),_GD=1,_GE=function(_GF){var _GG=new T(function(){return B(A(_GF,[_GD]));});return [1,B(_Gk(_GC,function(_GH){return E(_GG);}))];},_GI=function(_GJ){return [1,B(_Df(_GE,_Gy,_GJ))];},_GK=new T(function(){return B(unCStr("NUL"));}),_GL=0,_GM=function(_GN){var _GO=new T(function(){return B(A(_GN,[_GL]));});return [1,B(_Gk(_GK,function(_GP){return E(_GO);}))];},_GQ=new T(function(){return B(unCStr("STX"));}),_GR=2,_GS=function(_GT){var _GU=new T(function(){return B(A(_GT,[_GR]));});return [1,B(_Gk(_GQ,function(_GV){return E(_GU);}))];},_GW=new T(function(){return B(unCStr("ETX"));}),_GX=3,_GY=function(_GZ){var _H0=new T(function(){return B(A(_GZ,[_GX]));});return [1,B(_Gk(_GW,function(_H1){return E(_H0);}))];},_H2=new T(function(){return B(unCStr("EOT"));}),_H3=4,_H4=function(_H5){var _H6=new T(function(){return B(A(_H5,[_H3]));});return [1,B(_Gk(_H2,function(_H7){return E(_H6);}))];},_H8=new T(function(){return B(unCStr("ENQ"));}),_H9=5,_Ha=function(_Hb){var _Hc=new T(function(){return B(A(_Hb,[_H9]));});return [1,B(_Gk(_H8,function(_Hd){return E(_Hc);}))];},_He=new T(function(){return B(unCStr("ACK"));}),_Hf=6,_Hg=function(_Hh){var _Hi=new T(function(){return B(A(_Hh,[_Hf]));});return [1,B(_Gk(_He,function(_Hj){return E(_Hi);}))];},_Hk=new T(function(){return B(unCStr("BEL"));}),_Hl=7,_Hm=function(_Hn){var _Ho=new T(function(){return B(A(_Hn,[_Hl]));});return [1,B(_Gk(_Hk,function(_Hp){return E(_Ho);}))];},_Hq=new T(function(){return B(unCStr("BS"));}),_Hr=8,_Hs=function(_Ht){var _Hu=new T(function(){return B(A(_Ht,[_Hr]));});return [1,B(_Gk(_Hq,function(_Hv){return E(_Hu);}))];},_Hw=new T(function(){return B(unCStr("HT"));}),_Hx=9,_Hy=function(_Hz){var _HA=new T(function(){return B(A(_Hz,[_Hx]));});return [1,B(_Gk(_Hw,function(_HB){return E(_HA);}))];},_HC=new T(function(){return B(unCStr("LF"));}),_HD=10,_HE=function(_HF){var _HG=new T(function(){return B(A(_HF,[_HD]));});return [1,B(_Gk(_HC,function(_HH){return E(_HG);}))];},_HI=new T(function(){return B(unCStr("VT"));}),_HJ=11,_HK=function(_HL){var _HM=new T(function(){return B(A(_HL,[_HJ]));});return [1,B(_Gk(_HI,function(_HN){return E(_HM);}))];},_HO=new T(function(){return B(unCStr("FF"));}),_HP=12,_HQ=function(_HR){var _HS=new T(function(){return B(A(_HR,[_HP]));});return [1,B(_Gk(_HO,function(_HT){return E(_HS);}))];},_HU=new T(function(){return B(unCStr("CR"));}),_HV=13,_HW=function(_HX){var _HY=new T(function(){return B(A(_HX,[_HV]));});return [1,B(_Gk(_HU,function(_HZ){return E(_HY);}))];},_I0=new T(function(){return B(unCStr("SI"));}),_I1=15,_I2=function(_I3){var _I4=new T(function(){return B(A(_I3,[_I1]));});return [1,B(_Gk(_I0,function(_I5){return E(_I4);}))];},_I6=new T(function(){return B(unCStr("DLE"));}),_I7=16,_I8=function(_I9){var _Ia=new T(function(){return B(A(_I9,[_I7]));});return [1,B(_Gk(_I6,function(_Ib){return E(_Ia);}))];},_Ic=new T(function(){return B(unCStr("DC1"));}),_Id=17,_Ie=function(_If){var _Ig=new T(function(){return B(A(_If,[_Id]));});return [1,B(_Gk(_Ic,function(_Ih){return E(_Ig);}))];},_Ii=new T(function(){return B(unCStr("DC2"));}),_Ij=18,_Ik=function(_Il){var _Im=new T(function(){return B(A(_Il,[_Ij]));});return [1,B(_Gk(_Ii,function(_In){return E(_Im);}))];},_Io=new T(function(){return B(unCStr("DC3"));}),_Ip=19,_Iq=function(_Ir){var _Is=new T(function(){return B(A(_Ir,[_Ip]));});return [1,B(_Gk(_Io,function(_It){return E(_Is);}))];},_Iu=new T(function(){return B(unCStr("DC4"));}),_Iv=20,_Iw=function(_Ix){var _Iy=new T(function(){return B(A(_Ix,[_Iv]));});return [1,B(_Gk(_Iu,function(_Iz){return E(_Iy);}))];},_IA=new T(function(){return B(unCStr("NAK"));}),_IB=21,_IC=function(_ID){var _IE=new T(function(){return B(A(_ID,[_IB]));});return [1,B(_Gk(_IA,function(_IF){return E(_IE);}))];},_IG=new T(function(){return B(unCStr("SYN"));}),_IH=22,_II=function(_IJ){var _IK=new T(function(){return B(A(_IJ,[_IH]));});return [1,B(_Gk(_IG,function(_IL){return E(_IK);}))];},_IM=new T(function(){return B(unCStr("ETB"));}),_IN=23,_IO=function(_IP){var _IQ=new T(function(){return B(A(_IP,[_IN]));});return [1,B(_Gk(_IM,function(_IR){return E(_IQ);}))];},_IS=new T(function(){return B(unCStr("CAN"));}),_IT=24,_IU=function(_IV){var _IW=new T(function(){return B(A(_IV,[_IT]));});return [1,B(_Gk(_IS,function(_IX){return E(_IW);}))];},_IY=new T(function(){return B(unCStr("EM"));}),_IZ=25,_J0=function(_J1){var _J2=new T(function(){return B(A(_J1,[_IZ]));});return [1,B(_Gk(_IY,function(_J3){return E(_J2);}))];},_J4=new T(function(){return B(unCStr("SUB"));}),_J5=26,_J6=function(_J7){var _J8=new T(function(){return B(A(_J7,[_J5]));});return [1,B(_Gk(_J4,function(_J9){return E(_J8);}))];},_Ja=new T(function(){return B(unCStr("ESC"));}),_Jb=27,_Jc=function(_Jd){var _Je=new T(function(){return B(A(_Jd,[_Jb]));});return [1,B(_Gk(_Ja,function(_Jf){return E(_Je);}))];},_Jg=new T(function(){return B(unCStr("FS"));}),_Jh=28,_Ji=function(_Jj){var _Jk=new T(function(){return B(A(_Jj,[_Jh]));});return [1,B(_Gk(_Jg,function(_Jl){return E(_Jk);}))];},_Jm=new T(function(){return B(unCStr("GS"));}),_Jn=29,_Jo=function(_Jp){var _Jq=new T(function(){return B(A(_Jp,[_Jn]));});return [1,B(_Gk(_Jm,function(_Jr){return E(_Jq);}))];},_Js=new T(function(){return B(unCStr("RS"));}),_Jt=30,_Ju=function(_Jv){var _Jw=new T(function(){return B(A(_Jv,[_Jt]));});return [1,B(_Gk(_Js,function(_Jx){return E(_Jw);}))];},_Jy=new T(function(){return B(unCStr("US"));}),_Jz=31,_JA=function(_JB){var _JC=new T(function(){return B(A(_JB,[_Jz]));});return [1,B(_Gk(_Jy,function(_JD){return E(_JC);}))];},_JE=new T(function(){return B(unCStr("SP"));}),_JF=32,_JG=function(_JH){var _JI=new T(function(){return B(A(_JH,[_JF]));});return [1,B(_Gk(_JE,function(_JJ){return E(_JI);}))];},_JK=new T(function(){return B(unCStr("DEL"));}),_JL=127,_JM=function(_JN){var _JO=new T(function(){return B(A(_JN,[_JL]));});return [1,B(_Gk(_JK,function(_JP){return E(_JO);}))];},_JQ=[1,_JM,_3n],_JR=[1,_JG,_JQ],_JS=[1,_JA,_JR],_JT=[1,_Ju,_JS],_JU=[1,_Jo,_JT],_JV=[1,_Ji,_JU],_JW=[1,_Jc,_JV],_JX=[1,_J6,_JW],_JY=[1,_J0,_JX],_JZ=[1,_IU,_JY],_K0=[1,_IO,_JZ],_K1=[1,_II,_K0],_K2=[1,_IC,_K1],_K3=[1,_Iw,_K2],_K4=[1,_Iq,_K3],_K5=[1,_Ik,_K4],_K6=[1,_Ie,_K5],_K7=[1,_I8,_K6],_K8=[1,_I2,_K7],_K9=[1,_HW,_K8],_Ka=[1,_HQ,_K9],_Kb=[1,_HK,_Ka],_Kc=[1,_HE,_Kb],_Kd=[1,_Hy,_Kc],_Ke=[1,_Hs,_Kd],_Kf=[1,_Hm,_Ke],_Kg=[1,_Hg,_Kf],_Kh=[1,_Ha,_Kg],_Ki=[1,_H4,_Kh],_Kj=[1,_GY,_Ki],_Kk=[1,_GS,_Kj],_Kl=[1,_GM,_Kk],_Km=[1,_GI,_Kl],_Kn=new T(function(){return B(_Gc(_Km));}),_Ko=34,_Kp=[0,1114111],_Kq=92,_Kr=39,_Ks=function(_Kt){var _Ku=new T(function(){return B(A(_Kt,[_Hl]));}),_Kv=new T(function(){return B(A(_Kt,[_Hr]));}),_Kw=new T(function(){return B(A(_Kt,[_Hx]));}),_Kx=new T(function(){return B(A(_Kt,[_HD]));}),_Ky=new T(function(){return B(A(_Kt,[_HJ]));}),_Kz=new T(function(){return B(A(_Kt,[_HP]));}),_KA=new T(function(){return B(A(_Kt,[_HV]));}),_KB=new T(function(){return B(A(_Kt,[_Kq]));}),_KC=new T(function(){return B(A(_Kt,[_Kr]));}),_KD=new T(function(){return B(A(_Kt,[_Ko]));}),_KE=new T(function(){var _KF=function(_KG){var _KH=new T(function(){return B(_bz(E(_KG)));}),_KI=function(_KJ){var _KK=B(_Fp(_KH,_KJ));if(!B(_kR(_KK,_Kp))){return [2];}else{return new F(function(){return A(_Kt,[new T(function(){var _KL=B(_iN(_KK));if(_KL>>>0>1114111){return B(_ur(_KL));}else{return _KL;}})]);});}};return [1,B(_DW(_KG,_KI))];},_KM=new T(function(){var _KN=new T(function(){return B(A(_Kt,[_Jz]));}),_KO=new T(function(){return B(A(_Kt,[_Jt]));}),_KP=new T(function(){return B(A(_Kt,[_Jn]));}),_KQ=new T(function(){return B(A(_Kt,[_Jh]));}),_KR=new T(function(){return B(A(_Kt,[_Jb]));}),_KS=new T(function(){return B(A(_Kt,[_J5]));}),_KT=new T(function(){return B(A(_Kt,[_IZ]));}),_KU=new T(function(){return B(A(_Kt,[_IT]));}),_KV=new T(function(){return B(A(_Kt,[_IN]));}),_KW=new T(function(){return B(A(_Kt,[_IH]));}),_KX=new T(function(){return B(A(_Kt,[_IB]));}),_KY=new T(function(){return B(A(_Kt,[_Iv]));}),_KZ=new T(function(){return B(A(_Kt,[_Ip]));}),_L0=new T(function(){return B(A(_Kt,[_Ij]));}),_L1=new T(function(){return B(A(_Kt,[_Id]));}),_L2=new T(function(){return B(A(_Kt,[_I7]));}),_L3=new T(function(){return B(A(_Kt,[_I1]));}),_L4=new T(function(){return B(A(_Kt,[_Gx]));}),_L5=new T(function(){return B(A(_Kt,[_Hf]));}),_L6=new T(function(){return B(A(_Kt,[_H9]));}),_L7=new T(function(){return B(A(_Kt,[_H3]));}),_L8=new T(function(){return B(A(_Kt,[_GX]));}),_L9=new T(function(){return B(A(_Kt,[_GR]));}),_La=new T(function(){return B(A(_Kt,[_GD]));}),_Lb=new T(function(){return B(A(_Kt,[_GL]));}),_Lc=function(_Ld){switch(E(_Ld)){case 64:return E(_Lb);case 65:return E(_La);case 66:return E(_L9);case 67:return E(_L8);case 68:return E(_L7);case 69:return E(_L6);case 70:return E(_L5);case 71:return E(_Ku);case 72:return E(_Kv);case 73:return E(_Kw);case 74:return E(_Kx);case 75:return E(_Ky);case 76:return E(_Kz);case 77:return E(_KA);case 78:return E(_L4);case 79:return E(_L3);case 80:return E(_L2);case 81:return E(_L1);case 82:return E(_L0);case 83:return E(_KZ);case 84:return E(_KY);case 85:return E(_KX);case 86:return E(_KW);case 87:return E(_KV);case 88:return E(_KU);case 89:return E(_KT);case 90:return E(_KS);case 91:return E(_KR);case 92:return E(_KQ);case 93:return E(_KP);case 94:return E(_KO);case 95:return E(_KN);default:return [2];}};return B(_Ch([0,function(_Le){return (E(_Le)==94)?[0,_Lc]:[2];}],new T(function(){return B(A(_Kn,[_Kt]));})));});return B(_Ch([1,B(_Df(_G6,_G8,_KF))],_KM));});return new F(function(){return _Ch([0,function(_Lf){switch(E(_Lf)){case 34:return E(_KD);case 39:return E(_KC);case 92:return E(_KB);case 97:return E(_Ku);case 98:return E(_Kv);case 102:return E(_Kz);case 110:return E(_Kx);case 114:return E(_KA);case 116:return E(_Kw);case 118:return E(_Ky);default:return [2];}}],_KE);});},_Lg=function(_Lh){return new F(function(){return A(_Lh,[_a]);});},_Li=function(_Lj){var _Lk=E(_Lj);if(!_Lk[0]){return E(_Lg);}else{var _Ll=E(_Lk[1]),_Lm=_Ll>>>0,_Ln=new T(function(){return B(_Li(_Lk[2]));});if(_Lm>887){var _Lo=u_iswspace(_Ll);if(!E(_Lo)){return E(_Lg);}else{var _Lp=function(_Lq){var _Lr=new T(function(){return B(A(_Ln,[_Lq]));});return [0,function(_Ls){return E(_Lr);}];};return E(_Lp);}}else{var _Lt=E(_Lm);if(_Lt==32){var _Lu=function(_Lv){var _Lw=new T(function(){return B(A(_Ln,[_Lv]));});return [0,function(_Lx){return E(_Lw);}];};return E(_Lu);}else{if(_Lt-9>>>0>4){if(E(_Lt)==160){var _Ly=function(_Lz){var _LA=new T(function(){return B(A(_Ln,[_Lz]));});return [0,function(_LB){return E(_LA);}];};return E(_Ly);}else{return E(_Lg);}}else{var _LC=function(_LD){var _LE=new T(function(){return B(A(_Ln,[_LD]));});return [0,function(_LF){return E(_LE);}];};return E(_LC);}}}}},_LG=function(_LH){var _LI=new T(function(){return B(_LG(_LH));}),_LJ=function(_LK){return (E(_LK)==92)?E(_LI):[2];},_LL=function(_LM){return [0,_LJ];},_LN=[1,function(_LO){return new F(function(){return A(_Li,[_LO,_LL]);});}],_LP=new T(function(){return B(_Ks(function(_LQ){return new F(function(){return A(_LH,[[0,_LQ,_uq]]);});}));}),_LR=function(_LS){var _LT=E(_LS);if(_LT==38){return E(_LI);}else{var _LU=_LT>>>0;if(_LU>887){var _LV=u_iswspace(_LT);return (E(_LV)==0)?[2]:E(_LN);}else{var _LW=E(_LU);return (_LW==32)?E(_LN):(_LW-9>>>0>4)?(E(_LW)==160)?E(_LN):[2]:E(_LN);}}};return new F(function(){return _Ch([0,function(_LX){return (E(_LX)==92)?[0,_LR]:[2];}],[0,function(_LY){var _LZ=E(_LY);if(E(_LZ)==92){return E(_LP);}else{return new F(function(){return A(_LH,[[0,_LZ,_up]]);});}}]);});},_M0=function(_M1,_M2){var _M3=new T(function(){return B(A(_M2,[[1,new T(function(){return B(A(_M1,[_3n]));})]]));}),_M4=function(_M5){var _M6=E(_M5),_M7=E(_M6[1]);if(E(_M7)==34){if(!E(_M6[2])){return E(_M3);}else{return new F(function(){return _M0(function(_M8){return new F(function(){return A(_M1,[[1,_M7,_M8]]);});},_M2);});}}else{return new F(function(){return _M0(function(_M9){return new F(function(){return A(_M1,[[1,_M7,_M9]]);});},_M2);});}};return new F(function(){return _LG(_M4);});},_Ma=new T(function(){return B(unCStr("_\'"));}),_Mb=function(_Mc){var _Md=u_iswalnum(_Mc);if(!E(_Md)){return new F(function(){return _f5(_f4,_Mc,_Ma);});}else{return true;}},_Me=function(_Mf){return new F(function(){return _Mb(E(_Mf));});},_Mg=new T(function(){return B(unCStr(",;()[]{}`"));}),_Mh=new T(function(){return B(unCStr("=>"));}),_Mi=[1,_Mh,_3n],_Mj=new T(function(){return B(unCStr("~"));}),_Mk=[1,_Mj,_Mi],_Ml=new T(function(){return B(unCStr("@"));}),_Mm=[1,_Ml,_Mk],_Mn=new T(function(){return B(unCStr("->"));}),_Mo=[1,_Mn,_Mm],_Mp=new T(function(){return B(unCStr("<-"));}),_Mq=[1,_Mp,_Mo],_Mr=new T(function(){return B(unCStr("|"));}),_Ms=[1,_Mr,_Mq],_Mt=new T(function(){return B(unCStr("\\"));}),_Mu=[1,_Mt,_Ms],_Mv=new T(function(){return B(unCStr("="));}),_Mw=[1,_Mv,_Mu],_Mx=new T(function(){return B(unCStr("::"));}),_My=[1,_Mx,_Mw],_Mz=new T(function(){return B(unCStr(".."));}),_MA=[1,_Mz,_My],_MB=function(_MC){var _MD=new T(function(){return B(A(_MC,[_DT]));}),_ME=new T(function(){var _MF=new T(function(){var _MG=function(_MH){var _MI=new T(function(){return B(A(_MC,[[0,_MH]]));});return [0,function(_MJ){return (E(_MJ)==39)?E(_MI):[2];}];};return B(_Ks(_MG));}),_MK=function(_ML){var _MM=E(_ML);switch(E(_MM)){case 39:return [2];case 92:return E(_MF);default:var _MN=new T(function(){return B(A(_MC,[[0,_MM]]));});return [0,function(_MO){return (E(_MO)==39)?E(_MN):[2];}];}},_MP=new T(function(){var _MQ=new T(function(){return B(_M0(_Q,_MC));}),_MR=new T(function(){var _MS=new T(function(){var _MT=new T(function(){var _MU=function(_MV){var _MW=E(_MV),_MX=u_iswalpha(_MW);return (E(_MX)==0)?(E(_MW)==95)?[1,B(_DF(_Me,function(_MY){return new F(function(){return A(_MC,[[3,[1,_MW,_MY]]]);});}))]:[2]:[1,B(_DF(_Me,function(_MZ){return new F(function(){return A(_MC,[[3,[1,_MW,_MZ]]]);});}))];};return B(_Ch([0,_MU],new T(function(){return [1,B(_Df(_ER,_FW,_MC))];})));}),_N0=function(_N1){return (!B(_f5(_f4,_N1,_FY)))?[2]:[1,B(_DF(_FZ,function(_N2){var _N3=[1,_N1,_N2];if(!B(_f5(_CU,_N3,_MA))){return new F(function(){return A(_MC,[[4,_N3]]);});}else{return new F(function(){return A(_MC,[[2,_N3]]);});}}))];};return B(_Ch([0,_N0],_MT));});return B(_Ch([0,function(_N4){if(!B(_f5(_f4,_N4,_Mg))){return [2];}else{return new F(function(){return A(_MC,[[2,[1,_N4,_3n]]]);});}}],_MS));});return B(_Ch([0,function(_N5){return (E(_N5)==34)?E(_MQ):[2];}],_MR));});return B(_Ch([0,function(_N6){return (E(_N6)==39)?[0,_MK]:[2];}],_MP));});return new F(function(){return _Ch([1,function(_N7){return (E(_N7)[0]==0)?E(_MD):[2];}],_ME);});},_N8=0,_N9=function(_Na,_Nb){var _Nc=new T(function(){var _Nd=new T(function(){var _Ne=function(_Nf){var _Ng=new T(function(){var _Nh=new T(function(){return B(A(_Nb,[_Nf]));});return B(_MB(function(_Ni){var _Nj=E(_Ni);return (_Nj[0]==2)?(!B(_26(_Nj[1],_CL)))?[2]:E(_Nh):[2];}));}),_Nk=function(_Nl){return E(_Ng);};return [1,function(_Nm){return new F(function(){return A(_Li,[_Nm,_Nk]);});}];};return B(A(_Na,[_N8,_Ne]));});return B(_MB(function(_Nn){var _No=E(_Nn);return (_No[0]==2)?(!B(_26(_No[1],_CK)))?[2]:E(_Nd):[2];}));}),_Np=function(_Nq){return E(_Nc);};return function(_Nr){return new F(function(){return A(_Li,[_Nr,_Np]);});};},_Ns=function(_Nt,_Nu){var _Nv=function(_Nw){var _Nx=new T(function(){return B(A(_Nt,[_Nw]));}),_Ny=function(_Nz){return new F(function(){return _Ch(B(A(_Nx,[_Nz])),new T(function(){return [1,B(_N9(_Nv,_Nz))];}));});};return E(_Ny);},_NA=new T(function(){return B(A(_Nt,[_Nu]));}),_NB=function(_NC){return new F(function(){return _Ch(B(A(_NA,[_NC])),new T(function(){return [1,B(_N9(_Nv,_NC))];}));});};return E(_NB);},_ND=function(_NE,_NF){var _NG=function(_NH,_NI){var _NJ=function(_NK){return new F(function(){return A(_NI,[new T(function(){return  -E(_NK);})]);});},_NL=new T(function(){return B(_MB(function(_NM){return new F(function(){return A(_NE,[_NM,_NH,_NJ]);});}));}),_NN=function(_NO){return E(_NL);},_NP=function(_NQ){return new F(function(){return A(_Li,[_NQ,_NN]);});},_NR=new T(function(){return B(_MB(function(_NS){var _NT=E(_NS);if(_NT[0]==4){var _NU=E(_NT[1]);if(!_NU[0]){return new F(function(){return A(_NE,[_NT,_NH,_NI]);});}else{if(E(_NU[1])==45){if(!E(_NU[2])[0]){return [1,_NP];}else{return new F(function(){return A(_NE,[_NT,_NH,_NI]);});}}else{return new F(function(){return A(_NE,[_NT,_NH,_NI]);});}}}else{return new F(function(){return A(_NE,[_NT,_NH,_NI]);});}}));}),_NV=function(_NW){return E(_NR);};return [1,function(_NX){return new F(function(){return A(_Li,[_NX,_NV]);});}];};return new F(function(){return _Ns(_NG,_NF);});},_NY=function(_NZ){var _O0=E(_NZ);if(!_O0[0]){var _O1=_O0[2];return [1,new T(function(){return B(_F9(new T(function(){return B(_bz(E(_O0[1])));}),new T(function(){return B(_AZ(_O1,0));},1),B(_1A(_EZ,_O1))));})];}else{return (E(_O0[2])[0]==0)?(E(_O0[3])[0]==0)?[1,new T(function(){return B(_Fp(_EY,_O0[1]));})]:[0]:[0];}},_O2=function(_O3,_O4){return [2];},_O5=function(_O6){var _O7=E(_O6);if(_O7[0]==5){var _O8=B(_NY(_O7[1]));if(!_O8[0]){return E(_O2);}else{var _O9=new T(function(){return B(_iN(_O8[1]));});return function(_Oa,_Ob){return new F(function(){return A(_Ob,[_O9]);});};}}else{return E(_O2);}},_Oc=function(_Od){var _Oe=function(_Of){return [3,_Od,_D6];};return [1,function(_Og){return new F(function(){return A(_Li,[_Og,_Oe]);});}];},_Oh=new T(function(){return B(A(_ND,[_O5,_N8,_Oc]));}),_Oi=100,_Oj=[0,_6t,_6t,_6t,_6t,_up,_3n,_Oi],_Ok=function(_Ol){while(1){var _Om=B((function(_On){var _Oo=E(_On);if(!_Oo[0]){return [0];}else{var _Op=_Oo[2],_Oq=E(_Oo[1]);if(!E(_Oq[2])[0]){return [1,_Oq[1],new T(function(){return B(_Ok(_Op));})];}else{_Ol=_Op;return null;}}})(_Ol));if(_Om!=null){return _Om;}}},_Or=function(_Os){var _Ot=E(_Os);if(!_Ot[0]){return E(_C1);}else{var _Ou=new T(function(){var _Ov=B(_Ok(B(_C7(_Oh,new T(function(){return B(A(E(_Ot[1])[2],[_Oj,_3n]));})))));if(!_Ov[0]){return E(_C3);}else{if(!E(_Ov[2])[0]){return E(_Ov[1]);}else{return E(_C5);}}});return [0,_Ot[2],_Ou];}},_Ow=function(_Ox){return (E(_Ox)-48|0)>>>0<=9;},_Oy=0,_Oz=[1,_Oy],_OA=0,_OB=0,_OC=[1,_OB],_OD=1,_OE=[1,_OD],_OF=new T(function(){var _OG=B(_jX(_Ow,_3n)),_OH=_OG[2],_OI=E(_OG[1]);if(!_OI[0]){return [0,_OA,_OH];}else{return [0,new T(function(){var _OJ=B(_Ok(B(_C7(_Oh,_OI))));if(!_OJ[0]){return E(_C3);}else{if(!E(_OJ[2])[0]){return E(_OJ[1]);}else{return E(_C5);}}}),_OH];}}),_OK=new T(function(){return E(E(_OF)[1]);}),_OL=[1,_OK],_OM=new T(function(){return E(E(_OF)[2]);}),_ON=1,_OO=[1,_ON],_OP=function(_OQ,_OR,_OS,_OT,_OU,_OV){while(1){var _OW=B((function(_OX,_OY,_OZ,_P0,_P1,_P2){var _P3=E(_P1);if(!_P3[0]){return E(_fV);}else{var _P4=_P3[2],_P5=E(_P3[1]);switch(_P5){case 32:var _P6=_OX,_P7=_OY,_P8=_P0,_P9=_P2;_OQ=_P6;_OR=_P7;_OS=new T(function(){var _Pa=E(_OZ);if(!_Pa[0]){return E(_OE);}else{if(!E(_Pa[1])){return E(_OC);}else{return E(_OE);}}});_OT=_P8;_OU=_P4;_OV=_P9;return null;case 35:var _P6=_OX,_P7=_OY,_Pb=_OZ,_P9=_P2;_OQ=_P6;_OR=_P7;_OS=_Pb;_OT=_uq;_OU=_P4;_OV=_P9;return null;case 42:var _Pc=new T(function(){var _Pd=B(_Or(_P2));return [0,_Pd[1],_Pd[2]];}),_Pe=new T(function(){var _Pf=E(_P4);if(!_Pf[0]){return [0,_6t,_3n,new T(function(){return E(E(_Pc)[1]);})];}else{if(E(_Pf[1])==46){var _Pg=E(_Pf[2]);if(!_Pg[0]){return [0,_OL,_OM,new T(function(){return E(E(_Pc)[1]);})];}else{if(E(_Pg[1])==42){var _Ph=new T(function(){var _Pi=B(_Or(E(_Pc)[1]));return [0,_Pi[1],_Pi[2]];});return [0,[1,new T(function(){return E(E(_Ph)[2]);})],_Pg[2],new T(function(){return E(E(_Ph)[1]);})];}else{var _Pj=new T(function(){var _Pk=B(_jX(_Ow,_Pg)),_Pl=_Pk[2],_Pm=E(_Pk[1]);if(!_Pm[0]){return [0,_OA,_Pl];}else{return [0,new T(function(){var _Pn=B(_Ok(B(_C7(_Oh,_Pm))));if(!_Pn[0]){return E(_C3);}else{if(!E(_Pn[2])[0]){return E(_Pn[1]);}else{return E(_C5);}}}),_Pl];}});return [0,[1,new T(function(){return E(E(_Pj)[1]);})],new T(function(){return E(E(_Pj)[2]);}),new T(function(){return E(E(_Pc)[1]);})];}}}else{return [0,_6t,_Pf,new T(function(){return E(E(_Pc)[1]);})];}}}),_Po=new T(function(){return E(E(_Pe)[3]);}),_Pp=new T(function(){var _Pq=E(_Po);if(!_Pq[0]){return E(_C1);}else{return B(A(E(_Pq[1])[1],[new T(function(){return E(E(_Pe)[2]);})]));}}),_Pr=new T(function(){return E(E(_Pc)[2]);});return [0,[0,[1,new T(function(){return B(_rs(_Pr));})],new T(function(){return E(E(_Pe)[1]);}),new T(function(){if(E(_Pr)>=0){if(!E(_OX)){if(!E(_OY)){return [0];}else{return E(_OO);}}else{return E(_Oz);}}else{return E(_Oz);}}),_OZ,_P0,new T(function(){return E(E(_Pp)[1]);}),new T(function(){return E(E(_Pp)[2]);})],new T(function(){return E(E(_Pp)[3]);}),_Po];case 43:var _P6=_OX,_P7=_OY,_P8=_P0,_P9=_P2;_OQ=_P6;_OR=_P7;_OS=_OC;_OT=_P8;_OU=_P4;_OV=_P9;return null;case 45:var _P7=_OY,_Pb=_OZ,_P8=_P0,_P9=_P2;_OQ=_uq;_OR=_P7;_OS=_Pb;_OT=_P8;_OU=_P4;_OV=_P9;return null;case 46:var _Ps=new T(function(){var _Pt=E(_P4);if(!_Pt[0]){var _Pu=B(_jX(_Ow,_3n)),_Pv=_Pu[2],_Pw=E(_Pu[1]);if(!_Pw[0]){return [0,_OA,_Pv,_P2];}else{return [0,new T(function(){var _Px=B(_Ok(B(_C7(_Oh,_Pw))));if(!_Px[0]){return E(_C3);}else{if(!E(_Px[2])[0]){return E(_Px[1]);}else{return E(_C5);}}}),_Pv,_P2];}}else{if(E(_Pt[1])==42){var _Py=new T(function(){var _Pz=B(_Or(_P2));return [0,_Pz[1],_Pz[2]];});return [0,new T(function(){return E(E(_Py)[2]);}),_Pt[2],new T(function(){return E(E(_Py)[1]);})];}else{var _PA=B(_jX(_Ow,_Pt)),_PB=_PA[2],_PC=E(_PA[1]);if(!_PC[0]){return [0,_OA,_PB,_P2];}else{return [0,new T(function(){var _PD=B(_Ok(B(_C7(_Oh,_PC))));if(!_PD[0]){return E(_C3);}else{if(!E(_PD[2])[0]){return E(_PD[1]);}else{return E(_C5);}}}),_PB,_P2];}}}}),_PE=new T(function(){return E(E(_Ps)[3]);}),_PF=new T(function(){var _PG=E(_PE);if(!_PG[0]){return E(_C1);}else{return B(A(E(_PG[1])[1],[new T(function(){return E(E(_Ps)[2]);})]));}});return [0,[0,_6t,[1,new T(function(){return E(E(_Ps)[1]);})],new T(function(){if(!E(_OX)){if(!E(_OY)){return [0];}else{return E(_OO);}}else{return E(_Oz);}}),_OZ,_P0,new T(function(){return E(E(_PF)[1]);}),new T(function(){return E(E(_PF)[2]);})],new T(function(){return E(E(_PF)[3]);}),_PE];case 48:var _P6=_OX,_Pb=_OZ,_P8=_P0,_P9=_P2;_OQ=_P6;_OR=_uq;_OS=_Pb;_OT=_P8;_OU=_P4;_OV=_P9;return null;default:if((_P5-48|0)>>>0>9){var _PH=new T(function(){var _PI=E(_P2);if(!_PI[0]){return E(_C1);}else{return B(A(E(_PI[1])[1],[_P3]));}});return [0,[0,_6t,_6t,new T(function(){if(!E(_OX)){if(!E(_OY)){return [0];}else{return E(_OO);}}else{return E(_Oz);}}),_OZ,_P0,new T(function(){return E(E(_PH)[1]);}),new T(function(){return E(E(_PH)[2]);})],new T(function(){return E(E(_PH)[3]);}),_P2];}else{var _PJ=new T(function(){var _PK=B(_jX(_Ow,_P3)),_PL=_PK[2],_PM=E(_PK[1]);if(!_PM[0]){return [0,_OA,_PL];}else{return [0,new T(function(){var _PN=B(_Ok(B(_C7(_Oh,_PM))));if(!_PN[0]){return E(_C3);}else{if(!E(_PN[2])[0]){return E(_PN[1]);}else{return E(_C5);}}}),_PL];}}),_PO=new T(function(){var _PP=E(E(_PJ)[2]);if(!_PP[0]){return [0,_6t,_3n,_P2];}else{if(E(_PP[1])==46){var _PQ=E(_PP[2]);if(!_PQ[0]){return [0,_OL,_OM,_P2];}else{if(E(_PQ[1])==42){var _PR=new T(function(){var _PS=B(_Or(_P2));return [0,_PS[1],_PS[2]];});return [0,[1,new T(function(){return E(E(_PR)[2]);})],_PQ[2],new T(function(){return E(E(_PR)[1]);})];}else{var _PT=new T(function(){var _PU=B(_jX(_Ow,_PQ)),_PV=_PU[2],_PW=E(_PU[1]);if(!_PW[0]){return [0,_OA,_PV];}else{return [0,new T(function(){var _PX=B(_Ok(B(_C7(_Oh,_PW))));if(!_PX[0]){return E(_C3);}else{if(!E(_PX[2])[0]){return E(_PX[1]);}else{return E(_C5);}}}),_PV];}});return [0,[1,new T(function(){return E(E(_PT)[1]);})],new T(function(){return E(E(_PT)[2]);}),_P2];}}}else{return [0,_6t,_PP,_P2];}}}),_PY=new T(function(){return E(E(_PO)[3]);}),_PZ=new T(function(){var _Q0=E(_PY);if(!_Q0[0]){return E(_C1);}else{return B(A(E(_Q0[1])[1],[new T(function(){return E(E(_PO)[2]);})]));}}),_Q1=new T(function(){return E(E(_PJ)[1]);});return [0,[0,[1,new T(function(){return B(_rs(_Q1));})],new T(function(){return E(E(_PO)[1]);}),new T(function(){if(E(_Q1)>=0){if(!E(_OX)){if(!E(_OY)){return [0];}else{return E(_OO);}}else{return E(_Oz);}}else{return E(_Oz);}}),_OZ,_P0,new T(function(){return E(E(_PZ)[1]);}),new T(function(){return E(E(_PZ)[2]);})],new T(function(){return E(E(_PZ)[3]);}),_PY];}}}})(_OQ,_OR,_OS,_OT,_OU,_OV));if(_OW!=null){return _OW;}}},_Q2=37,_Q3=function(_Q4,_Q5,_Q6){var _Q7=E(_Q4);if(!_Q7[0]){return (E(_Q5)[0]==0)?E(_Q6):E(_fV);}else{var _Q8=_Q7[2],_Q9=E(_Q7[1]);if(E(_Q9)==37){var _Qa=function(_Qb){var _Qc=E(_Q5);if(!_Qc[0]){return E(_C1);}else{var _Qd=B(_OP(_up,_up,_6t,_up,_Q8,_Qc)),_Qe=E(_Qd[3]);if(!_Qe[0]){return E(_C1);}else{return new F(function(){return A(E(_Qe[1])[2],[_Qd[1],new T(function(){return B(_Q3(_Qd[2],_Qe[2],_Qb));})]);});}}},_Qf=E(_Q8);if(!_Qf[0]){return new F(function(){return _Qa(_Q6);});}else{if(E(_Qf[1])==37){return [1,_Q2,new T(function(){return B(_Q3(_Qf[2],_Q5,_Q6));})];}else{return new F(function(){return _Qa(_Q6);});}}}else{return [1,_Q9,new T(function(){return B(_Q3(_Q8,_Q5,_Q6));})];}}},_Qg=function(_Qh,_Qi){return new F(function(){return _1A(_BY,B(_Q3(_Qh,new T(function(){return B(_cu(_Qi,_3n));},1),_3n)));});},_Qj=new T(function(){return B(unCStr("%.3f"));}),_Qk=new T(function(){return B(unCStr("\""));}),_Ql=new T(function(){return B(unCStr("ccdtrans sav"));}),_Qm=new T(function(){return B(unCStr("  ccdacq"));}),_Qn=new T(function(){return B(unAppCStr("}",_fO));}),_Qo=new T(function(){return B(_16(_fO,_Qn));}),_Qp=new T(function(){return B(_7U(0,1,_3n));}),_Qq=new T(function(){return B(unCStr("1"));}),_Qr=new T(function(){return B(_16(_Qq,_3n));}),_Qs=[1,_fa,_Qr],_Qt=new T(function(){return B(_16(_Qp,_Qs));}),_Qu=[1,_fa,_Qt],_Qv=new T(function(){return B(_16(_Qk,_Qu));}),_Qw=[1,_fa,_Qv],_Qx=new T(function(){var _Qy=jsShow(0);return fromJSStr(_Qy);}),_Qz=new T(function(){var _QA=jsShow(4.0e-2);return fromJSStr(_QA);}),_QB=function(_QC){return new F(function(){return _Qg(_Qj,[1,[0,function(_QD){return new F(function(){return _fW(_QC,_QD);});},function(_QD){return new F(function(){return _BU(_QC,_QD);});}],_3n]);});},_QE=function(_QF,_QG,_QH,_QI){if(!E(_QF)){var _QJ=new T(function(){var _QK=new T(function(){var _QL=E(E(_QH)[1])[2],_QM=E(_QG);if(!E(_QM[7])){return E(_QM[4])+E(_QL)*25/900;}else{return E(_QM[5])+E(_QL)*25/900;}}),_QN=new T(function(){var _QO=new T(function(){var _QP=new T(function(){var _QQ=E(_QH),_QR=E(_QQ[1]),_QS=E(_QR[1]),_QT=E(_QQ[2]),_QU=E(_QT[1]),_QV=function(_QW){var _QX=new T(function(){var _QY=new T(function(){var _QZ=new T(function(){var _R0=new T(function(){var _R1=new T(function(){var _R2=new T(function(){var _R3=new T(function(){return E(E(_QG)[6])+12.5+(_QS*25/900-12.5)*Math.cos(E(_QI));}),_R4=new T(function(){var _R5=new T(function(){var _R6=new T(function(){return (E(E(_QG)[6])+12.5+(_QU*25/900-12.5)*Math.cos(E(_QI))-E(_R3))/_QW;}),_R7=new T(function(){var _R8=new T(function(){var _R9=new T(function(){var _Ra=new T(function(){return (_QS*25/900-12.5)*Math.sin(E(_QI));}),_Rb=new T(function(){var _Rc=new T(function(){var _Rd=new T(function(){return ((_QU*25/900-12.5)*Math.sin(E(_QI))-E(_Ra))/_QW;}),_Re=new T(function(){var _Rf=new T(function(){var _Rg=new T(function(){var _Rh=new T(function(){var _Ri=new T(function(){var _Rj=new T(function(){var _Rk=new T(function(){return B(_16(_Qz,[1,_fa,new T(function(){return B(_16(_QQ[3],_3n));})]));});return B(_16(B(_16(_Qm,[1,_fa,_Rk])),_Qo));},1);return B(_16(_fO,_Rj));});return B(unAppCStr("  umv tmp2 x",_Ri));},1);return B(_16(_fO,_Rh));});return B(unAppCStr("  umv sah y",_Rg));},1);return B(_16(_fO,_Rf));},1);return B(_16(B(_Qg(_Qj,[1,[0,function(_QD){return new F(function(){return _fW(_Rd,_QD);});},function(_QD){return new F(function(){return _BU(_Rd,_QD);});}],_3n])),_Re));});return B(unAppCStr("+i*",_Rc));},1);return B(_16(B(_QB(_Ra)),_Rb));});return B(unAppCStr("  x = ",_R9));},1);return B(_16(_fO,_R8));},1);return B(_16(B(_Qg(_Qj,[1,[0,function(_QD){return new F(function(){return _fW(_R6,_QD);});},function(_QD){return new F(function(){return _BU(_R6,_QD);});}],_3n])),_R7));});return B(unAppCStr("+i*",_R5));},1);return B(_16(B(_QB(_R3)),_R4));});return B(unAppCStr("  y = ",_R2));},1);return B(_16(_fO,_R1));});return B(unAppCStr("{",_R0));},1);return B(_16(_fO,_QZ));});return B(unAppCStr(";i+=1)",_QY));},1);return new F(function(){return _16(B(_7U(0,_QW,_3n)),_QX);});};if(_QS!=_QU){return B(_QV(B(_aU(_QS,_QU))));}else{return B(_QV(B(_aU(E(_QR[2]),E(_QT[2])))));}});return B(unAppCStr("for(i=0;i<=",_QP));},1);return B(_16(_fO,_QO));},1);return B(_16(B(_Qg(_Qj,[1,[0,function(_QD){return new F(function(){return _fW(_QK,_QD);});},function(_QD){return new F(function(){return _BU(_QK,_QD);});}],_3n])),_QN));});return new F(function(){return unAppCStr("umv sav ",_QJ);});}else{var _Rl=new T(function(){var _Rm=new T(function(){return E(E(_QG)[6])+12.5+(E(E(E(_QH)[1])[1])*25/900-12.5)*Math.cos(E(_QI));}),_Rn=new T(function(){var _Ro=new T(function(){var _Rp=new T(function(){return (E(E(E(_QH)[1])[1])*25/900-12.5)*Math.sin(E(_QI));}),_Rq=new T(function(){var _Rr=new T(function(){var _Rs=new T(function(){var _Rt=new T(function(){var _Ru=E(E(_QH)[1])[2],_Rv=E(_QG);if(!E(_Rv[7])){return E(_Rv[4])+E(_Ru)*25/900;}else{return E(_Rv[5])+E(_Ru)*25/900;}}),_Rw=new T(function(){var _Rx=new T(function(){var _Ry=E(E(_QH)[2])[2],_Rz=E(_QG);if(!E(_Rz[7])){return E(_Rz[4])+E(_Ry)*25/900;}else{return E(_Rz[5])+E(_Ry)*25/900;}}),_RA=new T(function(){var _RB=E(_QH),_RC=E(_RB[1]),_RD=E(_RC[1]),_RE=E(_RB[2]),_RF=E(_RE[1]),_RG=function(_RH){var _RI=new T(function(){var _RJ=new T(function(){var _RK=new T(function(){return B(_16(_Qk,[1,_fa,new T(function(){return B(_16(_RB[3],_Qw));})]));});return B(_16(_Qx,[1,_fa,_RK]));});return B(_16(_Qz,[1,_fa,_RJ]));});return new F(function(){return _16(B(_7U(0,_RH,_3n)),[1,_fa,_RI]);});};if(_RD!=_RF){return B(_RG(B(_aU(_RD,_RF))));}else{return B(_RG(B(_aU(E(_RC[2]),E(_RE[2])))));}});return B(_16(B(_Qg(_Qj,[1,[0,function(_QD){return new F(function(){return _fW(_Rx,_QD);});},function(_QD){return new F(function(){return _BU(_Rx,_QD);});}],_3n])),[1,_fa,_RA]));});return B(_16(B(_Qg(_Qj,[1,[0,function(_QD){return new F(function(){return _fW(_Rt,_QD);});},function(_QD){return new F(function(){return _BU(_Rt,_QD);});}],_3n])),[1,_fa,_Rw]));});return B(_16(_Ql,[1,_fa,_Rs]));},1);return B(_16(_fO,_Rr));},1);return B(_16(B(_Qg(_Qj,[1,[0,function(_QD){return new F(function(){return _fW(_Rp,_QD);});},function(_QD){return new F(function(){return _BU(_Rp,_QD);});}],_3n])),_Rq));});return B(unAppCStr(" tmp2 ",_Ro));},1);return B(_16(B(_Qg(_Qj,[1,[0,function(_QD){return new F(function(){return _fW(_Rm,_QD);});},function(_QD){return new F(function(){return _BU(_Rm,_QD);});}],_3n])),_Rn));});return new F(function(){return unAppCStr("umv sah ",_Rl);});}},_RL=function(_RM,_RN,_RO,_RP,_RQ,_RR){var _RS=[0,_fJ,_RM,_fK,_RN,_RO,_RP,_RQ,_RR],_RT=function(_RU){var _RV=new T(function(){var _RW=E(_RU),_RX=rintDouble(_RW*180/3.141592653589793),_RY=B(_bt(_RX)),_RZ=_RY[1],_S0=_RY[2],_S1=new T(function(){var _S2=new T(function(){var _S3=B(_1A(function(_S4){var _S5=E(_S4);if(E(E(_S5[1])[1])!=E(E(_S5[2])[1])){return new F(function(){return _QE(_fF,_RS,_S5,_RW);});}else{return new F(function(){return _QE(_fG,_RS,_S5,_RW);});}},B(_cu(_RM,_3n))));if(!_S3[0]){return [0];}else{return B(_fL([1,_S3[1],new T(function(){return B(_fQ(_fO,_S3[2]));})]));}},1);return B(_16(_fO,_S2));});if(_S0>=0){return B(_16(B(_fB(0,B(_cz(_RZ,_S0)),_3n)),_S1));}else{var _S6=hs_uncheckedIShiftRA64(B(_bL(_RZ)), -_S0);return B(_16(B(_fB(0,B(_bB(_S6)),_3n)),_S1));}});return new F(function(){return unAppCStr("umv sar ",_RV);});},_S7=B(_1A(_RT,_RR));if(!_S7[0]){return [0];}else{return new F(function(){return _fL([1,_S7[1],new T(function(){return B(_fQ(_fP,_S7[2]));})]);});}},_S8=(function(id){return document.getElementById(id);}),_S9=function(_Sa,_Sb){var _Sc=function(_){var _Sd=E(_S8)(E(_Sb)),_Se=__eq(_Sd,E(_8P));return (E(_Se)==0)?[1,_Sd]:_6t;};return new F(function(){return A(_2,[_Sa,_Sc]);});},_Sf=new T(function(){return encodeURIComponent;}),_Sg=new T(function(){return B(unCStr("data:text/plain;charset=utf-8,"));}),_Sh=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:190:3-9"));}),_Si=[0,_6t,_6u,_3n,_Sh,_6t,_6t],_Sj=new T(function(){return B(_6r(_Si));}),_Sk=new T(function(){return B(unCStr("href"));}),_Sl=function(_Sm){return new F(function(){return toJSStr(E(_Sm));});},_Sn=function(_So,_Sp,_){var _Sq=B(A(_S9,[_6B,new T(function(){return B(_Sl(_So));},1),_])),_Sr=E(_Sq);if(!_Sr[0]){return new F(function(){return die(_Sj);});}else{var _Ss=E(_Sf)(toJSStr(_Sp)),_St=E(_9t)(E(_Sr[1]),toJSStr(E(_Sk)),toJSStr(B(_16(_Sg,new T(function(){var _Su=String(_Ss);return fromJSStr(_Su);},1)))));return new F(function(){return _dQ(_);});}},_Sv=(function(ctx,rad){ctx.rotate(rad);}),_Sw=function(_Sx,_Sy,_Sz,_){var _SA=E(_dS)(_Sz),_SB=E(_Sv)(_Sz,E(_Sx)),_SC=B(A(_Sy,[_Sz,_])),_SD=E(_dR)(_Sz);return new F(function(){return _dQ(_);});},_SE=(function(ctx,x,y){ctx.translate(x,y);}),_SF=function(_SG,_SH,_SI,_SJ,_){var _SK=E(_dS)(_SJ),_SL=E(_SE)(_SJ,E(_SG),E(_SH)),_SM=B(A(_SI,[_SJ,_])),_SN=E(_dR)(_SJ);return new F(function(){return _dQ(_);});},_SO=function(_SP,_SQ,_SR,_SS,_ST,_SU,_SV,_SW){return new F(function(){return Math.atan((Math.tan(B(_mU(new T(function(){return B(_mc(_SS,_SQ));}),_SR-_SP))-1.5707963267948966)+Math.tan(B(_mU(new T(function(){return B(_mc(_SU,_SS));}),_ST-_SR)))+Math.tan(B(_mU(new T(function(){return B(_mc(_SW,_SU));}),_SV-_ST))+1.5707963267948966)+Math.tan(B(_mU(new T(function(){return B(_mc(_SQ,_SW));}),_SP-_SV))-3.141592653589793))/4);});},_SX=function(_SY){return E(_SY)/2;},_SZ=function(_T0,_T1,_T2,_){var _T3=E(_T0);return new F(function(){return _SF(_T3[1],_T3[2],_T1,E(_T2),_);});},_T4=function(_T5,_T6){var _T7=new T(function(){var _T8=E(_T5),_T9=E(E(_T6)[2]),_Ta=E(_T9[1]),_Tb=E(_Ta[1]),_Tc=E(_Ta[2]),_Td=E(_T9[2]),_Te=E(_Td[1]),_Tf=E(_Td[2]),_Tg=E(_T9[3]),_Th=E(_Tg[1]),_Ti=E(_Tg[2]),_Tj=E(_T9[4]),_Tk=E(_Tj[1]),_Tl=E(_Tj[2]);return Math.sqrt(E(_T8[1])*E(_T8[2])/(0.5*(_Tb*_Tl+_Tk*_Ti+_Th*_Tc-_Tb*_Ti-_Th*_Tl-_Tk*_Tc)+0.5*(_Tk*_Ti+_Th*_Tf+_Te*_Tl-_Tk*_Tf-_Te*_Ti-_Th*_Tl)));}),_Tm=new T(function(){var _Tn=E(_T5);return [0,new T(function(){return B(_SX(_Tn[1]));}),new T(function(){return B(_SX(_Tn[2]));})];}),_To=new T(function(){var _Tp=E(E(_T6)[2]),_Tq=E(_Tp[1]),_Tr=E(_Tp[2]),_Ts=E(_Tp[3]),_Tt=E(_Tp[4]);return  -B(_SO(E(_Tq[1]),_Tq[2],E(_Tr[1]),_Tr[2],E(_Ts[1]),_Ts[2],E(_Tt[1]),_Tt[2]));}),_Tu=new T(function(){var _Tv=E(E(_T6)[2]),_Tw=E(_Tv[1]),_Tx=E(_Tv[2]),_Ty=E(_Tv[3]),_Tz=E(_Tv[4]);return [0,new T(function(){return (E(_Tw[1])+E(_Tx[1])+E(_Ty[1])+E(_Tz[1]))/4/(-1);}),new T(function(){return (E(_Tw[2])+E(_Tx[2])+E(_Ty[2])+E(_Tz[2]))/4/(-1);})];}),_TA=function(_TB,_TC,_){var _TD=E(_Tm),_TE=function(_TF,_){var _TG=function(_TH,_){return new F(function(){return _Sw(_To,function(_TI,_){return new F(function(){return _SZ(_Tu,_TB,_TI,_);});},E(_TH),_);});};return new F(function(){return _dU(_T7,_T7,_TG,E(_TF),_);});};return new F(function(){return _SF(_TD[1],_TD[2],_TE,E(_TC),_);});};return E(_TA);},_TJ=(function(ctx,x,y){ctx.moveTo(x,y);}),_TK=(function(ctx,x,y){ctx.lineTo(x,y);}),_TL=function(_TM,_TN,_){var _TO=E(_TM);if(!_TO[0]){return _a;}else{var _TP=E(_TO[1]),_TQ=E(_TN),_TR=E(_TJ)(_TQ,E(_TP[1]),E(_TP[2])),_TS=E(_TO[2]);if(!_TS[0]){return _a;}else{var _TT=E(_TS[1]),_TU=E(_TK),_TV=_TU(_TQ,E(_TT[1]),E(_TT[2])),_TW=_TS[2];while(1){var _TX=E(_TW);if(!_TX[0]){return _a;}else{var _TY=E(_TX[1]),_TZ=_TU(_TQ,E(_TY[1]),E(_TY[2]));_TW=_TX[2];continue;}}}}},_U0=function(_U1,_U2,_){var _U3=new T(function(){return E(E(_U1)[2]);}),_U4=new T(function(){return E(E(_U3)[1]);});return new F(function(){return _TL([1,_U4,[1,new T(function(){return E(E(_U3)[2]);}),[1,new T(function(){return E(E(_U3)[3]);}),[1,new T(function(){return E(E(_U3)[4]);}),[1,_U4,_3n]]]]],_U2,_);});},_U5=(function(e){e.width = e.width;}),_U6=",",_U7="rgba(",_U8=new T(function(){return toJSStr(_3n);}),_U9="rgb(",_Ua=")",_Ub=[1,_Ua,_3n],_Uc=function(_Ud){var _Ue=E(_Ud);if(!_Ue[0]){var _Uf=jsCat([1,_U9,[1,new T(function(){return String(_Ue[1]);}),[1,_U6,[1,new T(function(){return String(_Ue[2]);}),[1,_U6,[1,new T(function(){return String(_Ue[3]);}),_Ub]]]]]],E(_U8));return E(_Uf);}else{var _Ug=jsCat([1,_U7,[1,new T(function(){return String(_Ue[1]);}),[1,_U6,[1,new T(function(){return String(_Ue[2]);}),[1,_U6,[1,new T(function(){return String(_Ue[3]);}),[1,_U6,[1,new T(function(){return String(_Ue[4]);}),_Ub]]]]]]]],E(_U8));return E(_Ug);}},_Uh="strokeStyle",_Ui="fillStyle",_Uj=(function(e,p){return e[p].toString();}),_Uk=function(_Ul,_Um){var _Un=new T(function(){return B(_Uc(_Ul));});return function(_Uo,_){var _Up=E(_Uo),_Uq=E(_Ui),_Ur=E(_Uj),_Us=_Ur(_Up,_Uq),_Ut=E(_Uh),_Uu=_Ur(_Up,_Ut),_Uv=E(_Un),_Uw=E(_1),_Ux=_Uw(_Up,_Uq,_Uv),_Uy=_Uw(_Up,_Ut,_Uv),_Uz=B(A(_Um,[_Up,_])),_UA=String(_Us),_UB=_Uw(_Up,_Uq,_UA),_UC=String(_Uu),_UD=_Uw(_Up,_Ut,_UC);return new F(function(){return _dQ(_);});};},_UE=function(_UF,_UG,_UH){var _UI=E(_UH);if(!_UI[0]){return [0];}else{var _UJ=_UI[1],_UK=_UI[2];return (!B(A(_UF,[_UG,_UJ])))?[1,_UJ,new T(function(){return B(_UE(_UF,_UG,_UK));})]:E(_UK);}},_UL="lineWidth",_UM=function(_UN,_UO){var _UP=new T(function(){return String(E(_UN));});return function(_UQ,_){var _UR=E(_UQ),_US=E(_UL),_UT=E(_Uj)(_UR,_US),_UU=E(_1),_UV=_UU(_UR,_US,E(_UP)),_UW=B(A(_UO,[_UR,_])),_UX=String(_UT),_UY=_UU(_UR,_US,_UX);return new F(function(){return _dQ(_);});};},_UZ=new T(function(){return B(unCStr("saveLink"));}),_V0=new T(function(){return B(unCStr("exportLink"));}),_V1=[0,255,0,255],_V2=1,_V3=0.2,_V4=900,_V5=[0,_V4,_V4],_V6=new T(function(){return B(unCStr("btn btn-primary"));}),_V7=new T(function(){return B(unCStr("class"));}),_V8=new T(function(){return B(unCStr("btn btn-primary disabled"));}),_V9="exportLink",_Va=new T(function(){return B(_S9(_6B,_V9));}),_Vb=new T(function(){return B(unCStr("value"));}),_Vc="runfile",_Vd=new T(function(){return B(_S9(_6B,_Vc));}),_Ve="scans",_Vf=new T(function(){return B(_S9(_6B,_Ve));}),_Vg=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:168:3-8"));}),_Vh=[0,_6t,_6u,_3n,_Vg,_6t,_6t],_Vi=new T(function(){return B(_6r(_Vh));}),_Vj=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:150:3-14"));}),_Vk=[0,_6t,_6u,_3n,_Vj,_6t,_6t],_Vl=new T(function(){return B(_6r(_Vk));}),_Vm=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:149:3-10"));}),_Vn=[0,_6t,_6u,_3n,_Vm,_6t,_6t],_Vo=new T(function(){return B(_6r(_Vn));}),_Vp=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:148:3-11"));}),_Vq=[0,_6t,_6u,_3n,_Vp,_6t,_6t],_Vr=new T(function(){return B(_6r(_Vq));}),_Vs="aligned",_Vt=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:147:3-11"));}),_Vu=[0,_6t,_6u,_3n,_Vt,_6t,_6t],_Vv=new T(function(){return B(_6r(_Vu));}),_Vw="original",_Vx=function(_Vy,_Vz,_){while(1){var _VA=E(_Vy);if(!_VA[0]){return _a;}else{var _VB=E(_VA[1]),_VC=B(_TL([1,_VB[1],[1,_VB[2],_3n]],_Vz,_));_Vy=_VA[2];continue;}}},_VD=[0,255,0,255],_VE=1,_VF=function(_VG){var _VH=new T(function(){var _VI=function(_BH,_VJ){return new F(function(){return _Vx(E(_VG)[2],_BH,_VJ);});};return B(_Uk(_VD,function(_VK,_){return new F(function(){return _e5(_VI,E(_VK),_);});}));});return new F(function(){return _UM(_VE,_VH);});},_VL=function(_VM){return new F(function(){return fromJSStr(E(_VM));});},_VN=function(_VO,_VP,_VQ,_VR){var _VS=new T(function(){var _VT=function(_){var _VU=E(_Uj)(B(A(_9r,[_VO,_VQ])),E(_VR));return new T(function(){return String(_VU);});};return E(_VT);});return new F(function(){return A(_2,[_VP,_VS]);});},_VV=function(_VW,_VX,_VY,_VZ){var _W0=B(_9i(_VX)),_W1=new T(function(){return B(_9o(_W0));}),_W2=function(_W3){return new F(function(){return A(_W1,[new T(function(){return B(_VL(_W3));})]);});},_W4=new T(function(){return B(_VN(_VW,_VX,_VY,new T(function(){return toJSStr(E(_VZ));},1)));});return new F(function(){return A(_9m,[_W0,_W4,_W2]);});},_W5=new T(function(){return B(unCStr("value"));}),_W6=function(_W7,_W8,_W9){var _Wa=E(_W9);if(!_Wa[0]){return [0];}else{var _Wb=_Wa[1],_Wc=_Wa[2];return (!B(A(_W7,[_Wb])))?[1,_Wb,new T(function(){return B(_W6(_W7,_W8,_Wc));})]:[1,new T(function(){return B(A(_W8,[_Wb]));}),new T(function(){return B(_W6(_W7,_W8,_Wc));})];}},_Wd=function(_We,_Wf,_Wg,_Wh,_){var _Wi=B(A(_VV,[_S,_6B,_Wg,_W5,_])),_Wj=_Wi,_Wk=E(_Wf),_Wl=rMV(_Wk),_Wm=E(_Wl),_Wn=new T(function(){return B(_W6(function(_Wo){return new F(function(){return _6O(_Wo,_Wh);});},function(_Wp){var _Wq=E(_Wp);return [0,_Wq[1],_Wq[2],_Wj];},_Wm[2]));}),_=wMV(_Wk,[0,_Wm[1],_Wn,_Wm[3],_Wm[4],_Wm[5],_Wm[6],_Wm[7],_Wm[8]]);return new F(function(){return A(_We,[_]);});},_Wr=function(_Ws,_Wt,_Wu,_){var _Wv=rMV(_Wt),_Ww=_Wv,_Wx=E(_Ws),_Wy=rMV(_Wx),_Wz=_Wy,_WA=B(A(_S9,[_6B,_Vw,_])),_WB=E(_WA);if(!_WB[0]){return new F(function(){return die(_Vv);});}else{var _WC=E(_WB[1]),_WD=E(_N),_WE=_WD(_WC);if(!_WE){return new F(function(){return die(_Vv);});}else{var _WF=E(_M),_WG=_WF(_WC),_WH=_WG,_WI=B(A(_S9,[_6B,_Vs,_])),_WJ=function(_,_WK){var _WL=E(_WK);if(!_WL[0]){return new F(function(){return die(_Vr);});}else{var _WM=B(A(_Vf,[_])),_WN=E(_WM);if(!_WN[0]){return new F(function(){return die(_Vo);});}else{var _WO=B(A(_Vd,[_])),_WP=E(_WO);if(!_WP[0]){return new F(function(){return die(_Vl);});}else{var _WQ=E(_Wz),_WR=_WQ[2],_WS=_WQ[8],_WT=E(_WQ[3]),_WU=E(_1)(E(_WP[1]),toJSStr(E(_Vb)),toJSStr(_WT)),_WV=B(A(_Va,[_])),_WW=E(_WV);if(!_WW[0]){return new F(function(){return die(_Vi);});}else{var _WX=_WW[1],_WY=function(_){var _WZ=function(_X0,_){var _X1=rMV(_Wx),_X2=E(_X1),_=wMV(_Wx,[0,_X2[1],new T(function(){return B(_UE(_6O,_X0,_X2[2]));}),_X2[3],_X2[4],_X2[5],_X2[6],_X2[7],_X2[8]]);return new F(function(){return _Wr(_Wx,_Wt,_Wu,_);});},_X3=function(_){return new F(function(){return _Wr(_Wx,_Wt,_Wu,_);});},_X4=B(_cD(function(_X5,_X6,_){return new F(function(){return _Wd(_X3,_Wx,_X5,_X6,_);});},_WZ,_WQ,E(_WN[1]),_)),_X7=E(_Wu),_X8=rMV(_X7),_X9=_X8,_Xa=E(_WL[1]),_Xb=_Xa[1],_Xc=E(_U5),_Xd=_Xc(_Xa[2]),_Xe=function(_Xf,_){return new F(function(){return _ec(E(_X9),0,0,E(_Xf),_);});},_Xg=B(A(_T4,[_V5,_Ww,function(_Xh,_){return new F(function(){return _dU(_V3,_V3,_Xe,E(_Xh),_);});},_Xb,_])),_Xi=B(A(_VF,[_WQ,_Xb,_])),_Xj=rMV(_X7),_Xk=_Xj,_Xl=_Xc(_WC),_Xm=B(_dU(_V3,_V3,function(_Xn,_){return new F(function(){return _ec(E(_Xk),0,0,E(_Xn),_);});},_WH,_)),_Xo=new T(function(){var _Xp=function(_X6,_){return new F(function(){return _U0(_Ww,_X6,_);});};return B(_Uk(_V1,function(_Xq,_){return new F(function(){return _e5(_Xp,E(_Xq),_);});}));}),_Xr=B(A(_UM,[_V2,_Xo,_WH,_])),_Xs=B(_Sn(_V0,new T(function(){return B(_RL(_WR,_WQ[4],_WQ[5],_WQ[6],_WQ[7],_WS));},1),_)),_Xt=new T(function(){return fromJSStr(B(_eU([4,E(B(_7C(_6Y,[1,new T(function(){return [4,E(B(_7g(_Ww)))];}),[1,new T(function(){return [4,E(B(_7H(_WQ)))];}),_3n]])))])));},1);return new F(function(){return _Sn(_UZ,_Xt,_);});};if(!B(_fh(_WR,_WT,_WS))){var _Xu=E(_9t)(E(_WX),toJSStr(E(_V7)),toJSStr(E(_V8)));return new F(function(){return _WY(_);});}else{var _Xv=E(_9t)(E(_WX),toJSStr(E(_V7)),toJSStr(E(_V6)));return new F(function(){return _WY(_);});}}}}}},_Xw=E(_WI);if(!_Xw[0]){return new F(function(){return _WJ(_,_6t);});}else{var _Xx=E(_Xw[1]),_Xy=_WD(_Xx);if(!_Xy){return new F(function(){return _WJ(_,_6t);});}else{var _Xz=_WF(_Xx);return new F(function(){return _WJ(_,[1,[0,_Xz,_Xx]]);});}}}}},_XA=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:101:3-9"));}),_XB=[0,_6t,_6u,_3n,_XA,_6t,_6t],_XC=new T(function(){return B(_6r(_XB));}),_XD=function(_){return new F(function(){return die(_XC);});},_XE=2,_XF=function(_XG){return E(_XG)[2];},_XH=function(_){return _6t;},_XI=function(_XJ,_){return new F(function(){return _XH(_);});},_XK=[0,_XF,_XI],_XL=function(_XM,_XN){while(1){var _XO=E(_XM);if(!_XO[0]){return E(_XN);}else{var _XP=_XO[2],_XQ=E(_XO[1]);if(_XN>_XQ){_XM=_XP;_XN=_XQ;continue;}else{_XM=_XP;continue;}}}},_XR=function(_XS,_XT,_XU){var _XV=E(_XS);if(_XU>_XV){return new F(function(){return _XL(_XT,_XV);});}else{return new F(function(){return _XL(_XT,_XU);});}},_XW=2,_XX=4,_XY=3,_XZ=function(_Y0,_Y1){var _Y2=function(_Y3,_Y4){while(1){var _Y5=B((function(_Y6,_Y7){var _Y8=E(_Y6);if(!_Y8[0]){return [0];}else{var _Y9=_Y8[2];if(!B(A(_Y0,[_Y8[1]]))){var _Ya=_Y7+1|0;_Y3=_Y9;_Y4=_Ya;return null;}else{return [1,_Y7,new T(function(){return B(_Y2(_Y9,_Y7+1|0));})];}}})(_Y3,_Y4));if(_Y5!=null){return _Y5;}}},_Yb=B(_Y2(_Y1,0));return (_Yb[0]==0)?[0]:[1,_Yb[1]];},_Yc=function(_Yd){return E(_Yd);},_Ye=function(_Yf,_Yg,_Yh,_){var _Yi=function(_Yj,_){var _Yk=E(_Yf),_Yl=rMV(_Yk),_Ym=E(E(_Yl)[2]),_Yn=new T(function(){var _Yo=new T(function(){var _Yp=E(E(_Yj)[1]);return [0,new T(function(){return B(_Yc(_Yp[1]));}),new T(function(){return B(_Yc(_Yp[2]));})];}),_Yq=new T(function(){var _Yr=E(_Yo),_Ys=E(_Ym[1]);return Math.pow(E(_Yr[1])-E(_Ys[1]),2)+Math.pow(E(_Yr[2])-E(_Ys[2]),2);}),_Yt=new T(function(){var _Yu=E(_Yo),_Yv=E(_Ym[2]);return Math.pow(E(_Yu[1])-E(_Yv[1]),2)+Math.pow(E(_Yu[2])-E(_Yv[2]),2);}),_Yw=[1,new T(function(){var _Yx=E(_Yo),_Yy=E(_Ym[3]);return Math.pow(E(_Yx[1])-E(_Yy[1]),2)+Math.pow(E(_Yx[2])-E(_Yy[2]),2);}),[1,new T(function(){var _Yz=E(_Yo),_YA=E(_Ym[4]);return Math.pow(E(_Yz[1])-E(_YA[1]),2)+Math.pow(E(_Yz[2])-E(_YA[2]),2);}),_3n]],_YB=new T(function(){return B(_XR(_Yt,_Yw,E(_Yq)));}),_YC=B(_XZ(function(_YD){return E(_YB)==E(_YD);},[1,_Yq,[1,_Yt,_Yw]]));if(!_YC[0]){return 3;}else{switch(E(_YC[1])){case 0:return 0;break;case 1:return 2;break;case 3:return 1;break;default:return 3;}}}),_=wMV(_Yk,[0,[1,_Yn],_Ym]);return new F(function(){return A(_Yh,[_]);});},_YE=B(A(_c2,[_6C,_XK,_9g,_Yg,_XW,_Yi,_])),_YF=B(A(_c2,[_6C,_XK,_9g,_Yg,_XY,function(_YG,_){var _YH=E(_Yf),_YI=rMV(_YH),_=wMV(_YH,[0,_1Q,E(_YI)[2]]);return new F(function(){return A(_Yh,[_]);});},_])),_YJ=function(_YK,_){var _YL=E(_Yf),_YM=rMV(_YL),_YN=E(_YM),_YO=_YN[2],_YP=E(_YN[1]);if(!_YP[0]){var _YQ=E(_YN);}else{var _YR=new T(function(){var _YS=E(E(_YK)[1]);return [0,new T(function(){return B(_Yc(_YS[1]));}),new T(function(){return B(_Yc(_YS[2]));})];});switch(E(_YP[1])){case 0:var _YT=E(_YO),_YU=[0,_YP,[0,_YR,_YT[2],_YT[3],_YT[4]]];break;case 1:var _YV=E(_YO),_YU=[0,_YP,[0,_YV[1],_YV[2],_YV[3],_YR]];break;case 2:var _YW=E(_YO),_YU=[0,_YP,[0,_YW[1],_YR,_YW[3],_YW[4]]];break;default:var _YX=E(_YO),_YU=[0,_YP,[0,_YX[1],_YX[2],_YR,_YX[4]]];}var _YQ=_YU;}var _=wMV(_YL,_YQ);return new F(function(){return A(_Yh,[_]);});},_YY=B(A(_c2,[_6C,_XK,_9g,_Yg,_XX,_YJ,_]));return _a;},_YZ=function(_Z0,_Z1,_Z2,_Z3,_Z4,_Z5,_Z6,_Z7,_Z8){if(!E(_Z1)){return [0,_2W,_Z2,_Z3,_Z4,_Z5,_Z6,_Z7,_Z8];}else{var _Z9=E(_Z2);if(!_Z9[0]){return [0,_2U,_3n,_Z3,_Z4,_Z5,_Z6,_Z7,_Z8];}else{var _Za=new T(function(){return E(E(_Z9[1])[1]);});return [0,_2U,[1,[0,_Za,new T(function(){var _Zb=E(_Za),_Zc=_Zb[1],_Zd=E(E(_Z0)[1]),_Ze=_Zd[1],_Zf=E(_Zd[2]),_Zg=E(_Zb[2]),_Zh=_Zf-_Zg;if(!_Zh){var _Zi=E(_Ze),_Zj=E(_Zc),_Zk=_Zi-_Zj;if(!_Zk){return [0,_Zi,_Zg];}else{if(_Zk<=0){if(0<= -_Zk){return [0,_Zi,_Zg];}else{return [0,_Zj,_Zf];}}else{if(0<=_Zk){return [0,_Zi,_Zg];}else{return [0,_Zj,_Zf];}}}}else{if(_Zh<=0){var _Zl=E(_Ze),_Zm=E(_Zc),_Zn=_Zl-_Zm;if(!_Zn){if( -_Zh<=0){return [0,_Zl,_Zg];}else{return [0,_Zm,_Zf];}}else{if(_Zn<=0){if( -_Zh<= -_Zn){return [0,_Zl,_Zg];}else{return [0,_Zm,_Zf];}}else{if( -_Zh<=_Zn){return [0,_Zl,_Zg];}else{return [0,_Zm,_Zf];}}}}else{var _Zo=E(_Ze),_Zp=E(_Zc),_Zq=_Zo-_Zp;if(!_Zq){return [0,_Zp,_Zf];}else{if(_Zq<=0){if(_Zh<= -_Zq){return [0,_Zo,_Zg];}else{return [0,_Zp,_Zf];}}else{if(_Zh<=_Zq){return [0,_Zo,_Zg];}else{return [0,_Zp,_Zf];}}}}}}),_3n],_Z9[2]],_Z3,_Z4,_Z5,_Z6,_Z7,_Z8];}}},_Zr=function(_Zs,_Zt,_Zu,_){var _Zv=function(_Zw,_){var _Zx=E(_Zs),_Zy=rMV(_Zx),_Zz=E(_Zy),_ZA=new T(function(){var _ZB=E(E(_Zw)[1]);return [0,new T(function(){return B(_Yc(_ZB[1]));}),new T(function(){return B(_Yc(_ZB[2]));})];}),_=wMV(_Zx,[0,_2U,[1,[0,_ZA,_ZA,_3n],_Zz[2]],_Zz[3],_Zz[4],_Zz[5],_Zz[6],_Zz[7],_Zz[8]]);return new F(function(){return A(_Zu,[_]);});},_ZC=B(A(_c2,[_6C,_XK,_9g,_Zt,_XW,_Zv,_])),_ZD=B(A(_c2,[_6C,_XK,_9g,_Zt,_XY,function(_ZE,_){var _ZF=E(_Zs),_ZG=rMV(_ZF),_ZH=E(_ZG),_ZI=B(_YZ(_ZE,_ZH[1],_ZH[2],_ZH[3],_ZH[4],_ZH[5],_ZH[6],_ZH[7],_ZH[8])),_=wMV(_ZF,[0,_2W,_ZI[2],_ZI[3],_ZI[4],_ZI[5],_ZI[6],_ZI[7],_ZI[8]]);return new F(function(){return A(_Zu,[_]);});},_])),_ZJ=B(A(_c2,[_6C,_XK,_9g,_Zt,_XX,function(_ZK,_){var _ZL=E(_Zs),_ZM=rMV(_ZL),_ZN=E(_ZM),_ZO=B(_YZ(_ZK,_ZN[1],_ZN[2],_ZN[3],_ZN[4],_ZN[5],_ZN[6],_ZN[7],_ZN[8])),_=wMV(_ZL,[0,_ZO[1],_ZO[2],_ZO[3],_ZO[4],_ZO[5],_ZO[6],_ZO[7],_ZO[8]]);return new F(function(){return A(_Zu,[_]);});},_]));return _a;},_ZP=new T(function(){return document;}),_ZQ=function(_ZR,_){var _ZS=E(_ZR);if(!_ZS[0]){return _3n;}else{var _ZT=B(_ZQ(_ZS[2],_));return [1,_ZS[1],_ZT];}},_ZU=function(_ZV,_){var _ZW=__arr2lst(0,_ZV);return new F(function(){return _ZQ(_ZW,_);});},_ZX=(function(e,q){if(!e || typeof e.querySelectorAll !== 'function') {return [];} else {return e.querySelectorAll(q);}}),_ZY=function(_ZZ,_100,_101){var _102=function(_){var _103=E(_ZX)(E(_100),toJSStr(E(_101)));return new F(function(){return _ZU(_103,_);});};return new F(function(){return A(_2,[_ZZ,_102]);});},_104=(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);}),_105=(function(x){return document.getElementById(x).value;}),_106=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_107=new T(function(){return B(err(_106));}),_108=function(_109){var _10a=E(_109);return (_10a[0]==0)?E(_107):E(_10a[1]);},_10b=0,_10c=[0,_10b,_10b],_10d=653,_10e=[0,_10d,_10b],_10f=986,_10g=[0,_10d,_10f],_10h=[0,_10b,_10f],_10i=[0,_10c,_10h,_10g,_10e],_10j=[0,_1Q,_10i],_10k=90,_10l=5,_10m=0,_10n=function(_10o,_10p,_10q){var _10r=E(_10p),_10s=E(_10q),_10t=new T(function(){var _10u=B(_uQ(_10o)),_10v=B(_10n(_10o,_10s,B(A(_sK,[_10u,new T(function(){return B(A(_tJ,[_10u,_10s,_10s]));}),_10r]))));return [1,_10v[1],_10v[2]];});return [0,_10r,_10t];},_10w=function(_10x){return E(E(_10x)[2]);},_10y=function(_10z){return E(E(_10z)[4]);},_10A=function(_10B){return E(E(_10B)[6]);},_10C=function(_10D,_10E){var _10F=E(_10E);if(!_10F[0]){return [0];}else{var _10G=_10F[1];return (!B(A(_10D,[_10G])))?[0]:[1,_10G,new T(function(){return B(_10C(_10D,_10F[2]));})];}},_10H=function(_10I,_10J,_10K,_10L,_10M){var _10N=B(_10n(_10J,_10K,_10L)),_10O=new T(function(){var _10P=new T(function(){return B(_uQ(_10J));}),_10Q=new T(function(){return B(A(_10w,[_10J,new T(function(){return B(A(_sK,[_10P,_10L,_10K]));}),new T(function(){return B(A(_sQ,[_10P,_sP]));})]));});if(!B(A(_10A,[_10I,_10L,_10K]))){var _10R=new T(function(){return B(A(_tJ,[_10P,_10M,_10Q]));});return function(_10S){return new F(function(){return A(_10A,[_10I,_10S,_10R]);});};}else{var _10T=new T(function(){return B(A(_tJ,[_10P,_10M,_10Q]));});return function(_10U){return new F(function(){return A(_10y,[_10I,_10U,_10T]);});};}});return new F(function(){return _10C(_10O,[1,_10N[1],_10N[2]]);});},_10V=new T(function(){return B(_10H(_oG,_mr,_10m,_10l,_10k));}),_10W=50,_10X=new T(function(){return B(unCStr("NA"));}),_10Y=[0,_2W,_3n,_10X,_10m,_10W,_10m,_2M,_10V],_10Z=new T(function(){return B(err(_C2));}),_110=new T(function(){return B(unCStr(".json"));}),_111="saveLink",_112=new T(function(){return B(unCStr("filePath"));}),_113=new T(function(){return B(unCStr("input[name=\'mount\']"));}),_114=new T(function(){return B(unCStr("IndianRoller2.jpg"));}),_115="loadPath",_116="filePath",_117=new T(function(){return B(err(_C4));}),_118=function(_119,_11a){return new F(function(){return A(_11a,[_2K]);});},_11b=[0,_2P,_118],_11c=[1,_11b,_3n],_11d=function(_11e,_11f){return new F(function(){return A(_11f,[_2M]);});},_11g=[0,_2O,_11d],_11h=[1,_11g,_11c],_11i=function(_11j,_11k,_11l){var _11m=E(_11j);if(!_11m[0]){return [2];}else{var _11n=E(_11m[1]),_11o=_11n[1],_11p=new T(function(){return B(A(_11n[2],[_11k,_11l]));}),_11q=new T(function(){return B(_MB(function(_11r){var _11s=E(_11r);switch(_11s[0]){case 3:return (!B(_26(_11o,_11s[1])))?[2]:E(_11p);case 4:return (!B(_26(_11o,_11s[1])))?[2]:E(_11p);default:return [2];}}));}),_11t=function(_11u){return E(_11q);};return new F(function(){return _Ch([1,function(_11v){return new F(function(){return A(_Li,[_11v,_11t]);});}],new T(function(){return B(_11i(_11m[2],_11k,_11l));}));});}},_11w=function(_11x,_11y){return new F(function(){return _11i(_11h,_11x,_11y);});},_11z=new T(function(){return B(A(_Ns,[_11w,_N8,_Oc]));}),_11A=new T(function(){return B(err(_C2));}),_11B=new T(function(){return B(err(_C4));}),_11C=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:50:3-15"));}),_11D=[0,_6t,_6u,_3n,_11C,_6t,_6t],_11E=new T(function(){return B(_6r(_11D));}),_11F=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:51:3-15"));}),_11G=[0,_6t,_6u,_3n,_11F,_6t,_6t],_11H=new T(function(){return B(_6r(_11G));}),_11I=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:52:3-14"));}),_11J=[0,_6t,_6u,_3n,_11I,_6t,_6t],_11K=new T(function(){return B(_6r(_11J));}),_11L=function(_11M,_11N){var _11O=function(_11P,_11Q){var _11R=function(_11S){return new F(function(){return A(_11Q,[new T(function(){return  -E(_11S);})]);});},_11T=new T(function(){return B(_MB(function(_11U){return new F(function(){return A(_11M,[_11U,_11P,_11R]);});}));}),_11V=function(_11W){return E(_11T);},_11X=function(_11Y){return new F(function(){return A(_Li,[_11Y,_11V]);});},_11Z=new T(function(){return B(_MB(function(_120){var _121=E(_120);if(_121[0]==4){var _122=E(_121[1]);if(!_122[0]){return new F(function(){return A(_11M,[_121,_11P,_11Q]);});}else{if(E(_122[1])==45){if(!E(_122[2])[0]){return [1,_11X];}else{return new F(function(){return A(_11M,[_121,_11P,_11Q]);});}}else{return new F(function(){return A(_11M,[_121,_11P,_11Q]);});}}}else{return new F(function(){return A(_11M,[_121,_11P,_11Q]);});}}));}),_123=function(_124){return E(_11Z);};return [1,function(_125){return new F(function(){return A(_Li,[_125,_123]);});}];};return new F(function(){return _Ns(_11O,_11N);});},_126=new T(function(){return 1/0;}),_127=function(_128,_129){return new F(function(){return A(_129,[_126]);});},_12a=new T(function(){return 0/0;}),_12b=function(_12c,_12d){return new F(function(){return A(_12d,[_12a]);});},_12e=new T(function(){return B(unCStr("NaN"));}),_12f=new T(function(){return B(unCStr("Infinity"));}),_12g=function(_12h,_12i){while(1){var _12j=E(_12h);if(!_12j[0]){var _12k=E(_12j[1]);if(_12k==(-2147483648)){_12h=[1,I_fromInt(-2147483648)];continue;}else{var _12l=E(_12i);if(!_12l[0]){return [0,_12k%_12l[1]];}else{_12h=[1,I_fromInt(_12k)];_12i=_12l;continue;}}}else{var _12m=_12j[1],_12n=E(_12i);return (_12n[0]==0)?[1,I_rem(_12m,I_fromInt(_12n[1]))]:[1,I_rem(_12m,_12n[1])];}}},_12o=function(_12p,_12q){if(!B(_iF(_12q,_sO))){return new F(function(){return _12g(_12p,_12q);});}else{return E(_iA);}},_12r=function(_12s,_12t){while(1){if(!B(_iF(_12t,_sO))){var _12u=_12t,_12v=B(_12o(_12s,_12t));_12s=_12u;_12t=_12v;continue;}else{return E(_12s);}}},_12w=function(_12x){var _12y=E(_12x);if(!_12y[0]){var _12z=E(_12y[1]);return (_12z==(-2147483648))?E(_lK):(_12z<0)?[0, -_12z]:E(_12y);}else{var _12A=_12y[1];return (I_compareInt(_12A,0)>=0)?E(_12y):[1,I_negate(_12A)];}},_12B=5,_12C=new T(function(){return B(_iw(_12B));}),_12D=new T(function(){return die(_12C);}),_12E=function(_12F,_12G){if(!B(_iF(_12G,_sO))){var _12H=B(_12r(B(_12w(_12F)),B(_12w(_12G))));return (!B(_iF(_12H,_sO)))?[0,B(_xf(_12F,_12H)),B(_xf(_12G,_12H))]:E(_iA);}else{return E(_12D);}},_12I=new T(function(){return B(_iF(_sP,_sO));}),_12J=function(_12K,_12L,_12M){while(1){if(!E(_12I)){if(!B(_iF(B(_12g(_12L,_sP)),_sO))){if(!B(_iF(_12L,_po))){var _12N=B(_si(_12K,_12K)),_12O=B(_xf(B(_l6(_12L,_po)),_sP)),_12P=B(_si(_12K,_12M));_12K=_12N;_12L=_12O;_12M=_12P;continue;}else{return new F(function(){return _si(_12K,_12M);});}}else{var _12N=B(_si(_12K,_12K)),_12O=B(_xf(_12L,_sP));_12K=_12N;_12L=_12O;continue;}}else{return E(_iA);}}},_12Q=function(_12R,_12S){while(1){if(!E(_12I)){if(!B(_iF(B(_12g(_12S,_sP)),_sO))){if(!B(_iF(_12S,_po))){return new F(function(){return _12J(B(_si(_12R,_12R)),B(_xf(B(_l6(_12S,_po)),_sP)),_12R);});}else{return E(_12R);}}else{var _12T=B(_si(_12R,_12R)),_12U=B(_xf(_12S,_sP));_12R=_12T;_12S=_12U;continue;}}else{return E(_iA);}}},_12V=function(_12W,_12X){if(!B(_fs(_12X,_sO))){if(!B(_iF(_12X,_sO))){return new F(function(){return _12Q(_12W,_12X);});}else{return E(_po);}}else{return E(_tv);}},_12Y=[0,1],_12Z=[0,0],_130=[0,-1],_131=function(_132){var _133=E(_132);if(!_133[0]){var _134=_133[1];return (_134>=0)?(E(_134)==0)?E(_12Z):E(_jn):E(_130);}else{var _135=I_compareInt(_133[1],0);return (_135<=0)?(E(_135)==0)?E(_12Z):E(_130):E(_jn);}},_136=function(_137,_138,_139){while(1){var _13a=E(_139);if(!_13a[0]){if(!B(_fs(_137,_F8))){return [0,B(_si(_138,B(_12V(_EY,_137)))),_po];}else{var _13b=B(_12V(_EY,B(_lL(_137))));return new F(function(){return _12E(B(_si(_138,B(_131(_13b)))),B(_12w(_13b)));});}}else{var _13c=B(_l6(_137,_12Y)),_13d=B(_iQ(B(_si(_138,_EY)),B(_bz(E(_13a[1])))));_137=_13c;_138=_13d;_139=_13a[2];continue;}}},_13e=function(_13f,_13g){var _13h=E(_13f);if(!_13h[0]){var _13i=_13h[1],_13j=E(_13g);return (_13j[0]==0)?_13i>=_13j[1]:I_compareInt(_13j[1],_13i)<=0;}else{var _13k=_13h[1],_13l=E(_13g);return (_13l[0]==0)?I_compareInt(_13k,_13l[1])>=0:I_compare(_13k,_13l[1])>=0;}},_13m=function(_13n){var _13o=E(_13n);if(!_13o[0]){var _13p=_13o[2];return new F(function(){return _12E(B(_si(B(_F9(new T(function(){return B(_bz(E(_13o[1])));}),new T(function(){return B(_AZ(_13p,0));},1),B(_1A(_EZ,_13p)))),_12Y)),_12Y);});}else{var _13q=_13o[1],_13r=_13o[3],_13s=E(_13o[2]);if(!_13s[0]){var _13t=E(_13r);if(!_13t[0]){return new F(function(){return _12E(B(_si(B(_Fp(_EY,_13q)),_12Y)),_12Y);});}else{var _13u=_13t[1];if(!B(_13e(_13u,_F8))){var _13v=B(_12V(_EY,B(_lL(_13u))));return new F(function(){return _12E(B(_si(B(_Fp(_EY,_13q)),B(_131(_13v)))),B(_12w(_13v)));});}else{return new F(function(){return _12E(B(_si(B(_si(B(_Fp(_EY,_13q)),B(_12V(_EY,_13u)))),_12Y)),_12Y);});}}}else{var _13w=_13s[1],_13x=E(_13r);if(!_13x[0]){return new F(function(){return _136(_F8,B(_Fp(_EY,_13q)),_13w);});}else{return new F(function(){return _136(_13x[1],B(_Fp(_EY,_13q)),_13w);});}}}},_13y=function(_13z,_13A){while(1){var _13B=E(_13A);if(!_13B[0]){return [0];}else{if(!B(A(_13z,[_13B[1]]))){return E(_13B);}else{_13A=_13B[2];continue;}}}},_13C=0,_13D=function(_13E){return new F(function(){return _rG(_13C,_13E);});},_13F=[0,E(_F8),E(_po)],_13G=[1,_13F],_13H=[0,-2147483648],_13I=[0,2147483647],_13J=function(_13K,_13L,_13M){var _13N=E(_13M);if(!_13N[0]){return [1,new T(function(){var _13O=B(_13m(_13N));return [0,E(_13O[1]),E(_13O[2])];})];}else{var _13P=E(_13N[3]);if(!_13P[0]){return [1,new T(function(){var _13Q=B(_13m(_13N));return [0,E(_13Q[1]),E(_13Q[2])];})];}else{var _13R=_13P[1];if(!B(_jf(_13R,_13I))){if(!B(_fs(_13R,_13H))){var _13S=function(_13T){var _13U=_13T+B(_iN(_13R))|0;return (_13U<=(E(_13L)+3|0))?(_13U>=(E(_13K)-3|0))?[1,new T(function(){var _13V=B(_13m(_13N));return [0,E(_13V[1]),E(_13V[2])];})]:E(_13G):[0];},_13W=B(_13y(_13D,_13N[1]));if(!_13W[0]){var _13X=E(_13N[2]);if(!_13X[0]){return E(_13G);}else{var _13Y=B(_jX(_13D,_13X[1]));if(!E(_13Y[2])[0]){return E(_13G);}else{return new F(function(){return _13S( -B(_AZ(_13Y[1],0)));});}}}else{return new F(function(){return _13S(B(_AZ(_13W,0)));});}}else{return [0];}}else{return [0];}}}},_13Z=function(_140){var _141=E(_140);switch(_141[0]){case 3:var _142=_141[1];return (!B(_26(_142,_12f)))?(!B(_26(_142,_12e)))?E(_O2):E(_12b):E(_127);case 5:var _143=B(_13J(_nC,_nB,_141[1]));if(!_143[0]){return E(_127);}else{var _144=new T(function(){var _145=E(_143[1]);return B(_lT(_145[1],_145[2]));});return function(_146,_147){return new F(function(){return A(_147,[_144]);});};}break;default:return E(_O2);}},_148=new T(function(){return B(A(_11L,[_13Z,_N8,_Oc]));}),_149=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:53:3-11"));}),_14a=[0,_6t,_6u,_3n,_149,_6t,_6t],_14b=new T(function(){return B(_6r(_14a));}),_14c=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:62:3-10"));}),_14d=[0,_6t,_6u,_3n,_14c,_6t,_6t],_14e=new T(function(){return B(_6r(_14d));}),_14f=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:63:3-11"));}),_14g=[0,_6t,_6u,_3n,_14f,_6t,_6t],_14h=new T(function(){return B(_6r(_14g));}),_14i=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:72:3-12"));}),_14j=[0,_6t,_6u,_3n,_14i,_6t,_6t],_14k=new T(function(){return B(_6r(_14j));}),_14l=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:73:3-12"));}),_14m=[0,_6t,_6u,_3n,_14l,_6t,_6t],_14n=new T(function(){return B(_6r(_14m));}),_14o=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:74:3-11"));}),_14p=[0,_6t,_6u,_3n,_14o,_6t,_6t],_14q=new T(function(){return B(_6r(_14p));}),_14r=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:89:3-14"));}),_14s=[0,_6t,_6u,_3n,_14r,_6t,_6t],_14t=new T(function(){return B(_6r(_14s));}),_14u=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:90:3-11"));}),_14v=[0,_6t,_6u,_3n,_14u,_6t,_6t],_14w=new T(function(){return B(_6r(_14v));}),_14x=new T(function(){return B(unCStr("input[name=\'mount\']:checked"));}),_14y="offset",_14z="bottom",_14A="top",_14B=function(_14C,_14D){return [1,new T(function(){var _14E=B(_Ok(B(_C7(_148,_14C))));if(!_14E[0]){return E(_11A);}else{if(!E(_14E[2])[0]){return E(_14E[1])*1.7453292519943295e-2;}else{return E(_11B);}}}),_14D];},_14F="rotations",_14G=new T(function(){return B(unCStr("loadPath"));}),_14H=function(_14I,_){var _14J=function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);},_14K=E(_14J)("processDump",toJSStr(_14G));return new F(function(){return _dQ(_);});},_14L=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:121:5-17"));}),_14M=[0,_6t,_6u,_3n,_14L,_6t,_6t],_14N=new T(function(){return B(_6r(_14M));}),_14O=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:124:5-19"));}),_14P=[0,_6t,_6u,_3n,_14O,_6t,_6t],_14Q=new T(function(){return B(_6r(_14P));}),_14R=new T(function(){return B(unCStr(".txt"));}),_14S=new T(function(){return B(unCStr("download"));}),_14T=function(_14U,_14V){var _14W=E(_14V);if(!_14W[0]){return [0,_3n,_3n];}else{var _14X=_14W[1];if(!B(A(_14U,[_14X]))){var _14Y=new T(function(){var _14Z=B(_14T(_14U,_14W[2]));return [0,_14Z[1],_14Z[2]];});return [0,[1,_14X,new T(function(){return E(E(_14Y)[1]);})],new T(function(){return E(E(_14Y)[2]);})];}else{return [0,_3n,_14W];}}},_150=function(_151){var _152=_151>>>0;if(_152>887){var _153=u_iswspace(_151);return (E(_153)==0)?false:true;}else{var _154=E(_152);return (_154==32)?true:(_154-9>>>0>4)?(E(_154)==160)?true:false:true;}},_155=function(_156){return new F(function(){return _150(E(_156));});},_157=function(_158,_159,_15a){var _15b=function(_15c){var _15d=B(_13y(_155,_15c));if(!_15d[0]){return E(_159);}else{var _15e=new T(function(){var _15f=B(_14T(_155,_15d));return [0,_15f[1],_15f[2]];});return new F(function(){return A(_158,[new T(function(){return E(E(_15e)[1]);}),new T(function(){return B(_15b(E(_15e)[2]));})]);});}};return new F(function(){return _15b(_15a);});},_15g=function(_){var _15h=B(A(_S9,[_6B,_116,_])),_15i=E(_15h);if(!_15i[0]){return new F(function(){return die(_11E);});}else{var _15j=B(A(_S9,[_6B,_115,_])),_15k=E(_15j);if(!_15k[0]){return new F(function(){return die(_11H);});}else{var _15l=B(A(_S9,[_6B,_Vc,_])),_15m=E(_15l);if(!_15m[0]){return new F(function(){return die(_11K);});}else{var _15n=_15m[1],_15o=B(A(_S9,[_6B,_14F,_])),_15p=E(_15o);if(!_15p[0]){return new F(function(){return die(_14b);});}else{var _15q=_15p[1],_15r=nMV(_10j),_15s=_15r,_15t=nMV(_10Y),_15u=_15t,_15v=B(A(_5,[_6B,_114,_])),_15w=nMV(_15v),_15x=_15w,_15y=nMV(_114),_15z=_15y,_15A=B(A(_S9,[_6B,_Vw,_])),_15B=E(_15A);if(!_15B[0]){return new F(function(){return die(_14e);});}else{var _15C=E(_15B[1]),_15D=E(_N),_15E=_15D(_15C);if(!_15E){return new F(function(){return die(_14e);});}else{var _15F=E(_M),_15G=_15F(_15C),_15H=_15G,_15I=B(A(_S9,[_6B,_Vs,_])),_15J=function(_,_15K){var _15L=E(_15K);if(!_15L[0]){return new F(function(){return die(_14h);});}else{var _15M=function(_){return new F(function(){return _Wr(_15u,_15s,_15x,_);});},_15N=B(_Ye(_15s,[0,_15H,_15C],_15M,_)),_15O=B(_Zr(_15u,_15L[1],_15M,_)),_15P=function(_15Q,_){var _15R=String(E(_15Q)),_15S=jsParseJSON(_15R);if(!_15S[0]){return _8P;}else{var _15T=B(_4e(_15S[1]));if(!_15T[0]){return _8P;}else{var _15U=_15T[1],_=wMV(_15s,new T(function(){return E(E(_15U)[1]);})),_=wMV(_15u,new T(function(){return E(E(_15U)[2]);}));return _8P;}}},_15V=__createJSFunc(2,E(_15P)),_15W=(function(s,f){Haste[s] = f;}),_15X=E(_15W)("processDump",_15V),_15Y=B(A(_S9,[_6B,_14A,_])),_15Z=E(_15Y);if(!_15Z[0]){return new F(function(){return die(_14k);});}else{var _160=_15Z[1],_161=B(A(_S9,[_6B,_14z,_])),_162=E(_161);if(!_162[0]){return new F(function(){return die(_14n);});}else{var _163=_162[1],_164=B(A(_S9,[_6B,_14y,_])),_165=E(_164);if(!_165[0]){return new F(function(){return die(_14q);});}else{var _166=_165[1],_167=B(A(_ZY,[_6B,_ZP,_113,_])),_168=function(_169,_){var _16a=E(_169),_16b=toJSStr(_112),_16c=E(_104)(_16b),_16d=B(A(_5,[_6B,new T(function(){var _16e=String(_16c);return fromJSStr(_16e);}),_])),_=wMV(_15x,_16d),_16f=E(_105)(_16b),_16g=new T(function(){var _16h=String(_16f);return fromJSStr(_16h);}),_=wMV(_15z,_16g),_16i=B(A(_S9,[_6B,_111,_])),_16j=E(_16i);if(!_16j[0]){return new F(function(){return die(_14N);});}else{var _16k=toJSStr(E(_14S)),_16l=E(_9t),_16m=_16l(E(_16j[1]),_16k,toJSStr(B(_16(_16g,_110)))),_16n=B(A(_S9,[_6B,_V9,_])),_16o=E(_16n);if(!_16o[0]){return new F(function(){return die(_14Q);});}else{var _16p=_16l(E(_16o[1]),_16k,toJSStr(B(_16(_16g,_14R))));return new F(function(){return _Wr(_15u,_15s,_15x,_);});}}},_16q=B(A(_c2,[_6C,_S,_o,_15i[1],_b4,_168,_])),_16r=B(A(_c2,[_6C,_S,_o,_15k[1],_b4,_14H,_])),_16s=function(_){var _16t=B(A(_S9,[_6B,_Vc,_])),_16u=E(_16t);if(!_16u[0]){return new F(function(){return die(_14t);});}else{var _16v=B(A(_S9,[_6B,_14F,_])),_16w=E(_16v);if(!_16w[0]){return new F(function(){return die(_14w);});}else{var _16x=B(A(_VV,[_S,_6B,_16u[1],_Vb,_])),_16y=rMV(_15u),_16z=E(_16y),_=wMV(_15u,[0,_16z[1],_16z[2],_16x,_16z[4],_16z[5],_16z[6],_16z[7],_16z[8]]),_16A=B(A(_VV,[_S,_6B,_16w[1],_Vb,_])),_16B=rMV(_15u),_16C=E(_16B),_=wMV(_15u,[0,_16C[1],_16C[2],_16C[3],_16C[4],_16C[5],_16C[6],_16C[7],new T(function(){return B(_157(_14B,_3n,_16A));})]),_16D=B(A(_S9,[_6B,_14A,_])),_16E=B(A(_VV,[_S,_6B,new T(function(){return B(_108(_16D));}),_Vb,_])),_16F=B(A(_S9,[_6B,_14z,_])),_16G=B(A(_VV,[_S,_6B,new T(function(){return B(_108(_16F));}),_Vb,_])),_16H=B(A(_S9,[_6B,_14y,_])),_16I=B(A(_VV,[_S,_6B,new T(function(){return B(_108(_16H));}),_Vb,_])),_16J=B(A(_ZY,[_6B,_ZP,_14x,_])),_16K=E(_16J);if(!_16K[0]){return new F(function(){return _XD(_);});}else{if(!E(_16K[2])[0]){var _16L=B(A(_VV,[_S,_6B,_16K[1],_Vb,_])),_16M=rMV(_15u),_16N=E(_16M),_=wMV(_15u,[0,_16N[1],_16N[2],_16N[3],new T(function(){var _16O=B(_Ok(B(_C7(_148,_16E))));if(!_16O[0]){return E(_11A);}else{if(!E(_16O[2])[0]){return E(_16O[1]);}else{return E(_11B);}}}),new T(function(){var _16P=B(_Ok(B(_C7(_148,_16G))));if(!_16P[0]){return E(_11A);}else{if(!E(_16P[2])[0]){return E(_16P[1]);}else{return E(_11B);}}}),new T(function(){var _16Q=B(_Ok(B(_C7(_148,_16I))));if(!_16Q[0]){return E(_11A);}else{if(!E(_16Q[2])[0]){return E(_16Q[1]);}else{return E(_11B);}}}),new T(function(){var _16R=B(_Ok(B(_C7(_11z,_16L))));if(!_16R[0]){return E(_10Z);}else{if(!E(_16R[2])[0]){return E(_16R[1]);}else{return E(_117);}}}),_16N[8]]);return new F(function(){return _Wr(_15u,_15s,_15x,_);});}else{return new F(function(){return _XD(_);});}}}}},_16S=function(_16T,_){return new F(function(){return _16s(_);});},_16U=function(_16V,_){while(1){var _16W=E(_16V);if(!_16W[0]){var _16X=B(A(_c2,[_6C,_S,_o,_15n,_b4,_16S,_])),_16Y=B(A(_c2,[_6C,_S,_o,_15q,_b4,_16S,_])),_16Z=B(A(_c2,[_6C,_S,_o,_160,_b4,_16S,_])),_170=B(A(_c2,[_6C,_S,_o,_163,_b4,_16S,_])),_171=B(A(_c2,[_6C,_S,_o,_166,_b4,_16S,_]));return _a;}else{var _172=B(A(_c2,[_6C,_S,_o,_16W[1],_b4,_16S,_]));_16V=_16W[2];continue;}}},_173=B(_16U(_167,_)),_174=B(A(_c2,[_6C,_S,_L,_15n,_XE,_16S,_])),_175=B(A(_c2,[_6C,_S,_L,_15q,_XE,_16S,_])),_176=B(A(_c2,[_6C,_S,_L,_160,_XE,_16S,_])),_177=B(A(_c2,[_6C,_S,_L,_163,_XE,_16S,_])),_178=B(A(_c2,[_6C,_S,_L,_166,_XE,_16S,_]));return new F(function(){return _Wr(_15u,_15s,_15x,_);});}}}}},_179=E(_15I);if(!_179[0]){return new F(function(){return _15J(_,_6t);});}else{var _17a=E(_179[1]),_17b=_15D(_17a);if(!_17b){return new F(function(){return _15J(_,_6t);});}else{var _17c=_15F(_17a);return new F(function(){return _15J(_,[1,[0,_17c,_17a]]);});}}}}}}}}},_17d=function(_){return new F(function(){return _15g(_);});};
var hasteMain = function() {B(A(_17d, [0]));};window.onload = hasteMain;