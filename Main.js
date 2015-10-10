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

var _0="src",_1=(function(e,p,v){e[p] = v;}),_2=function(_3){return E(E(_3)[2]);},_4=(function(t){return document.createElement(t);}),_5=function(_6,_7){return new F(function(){return A(_2,[_6,function(_){var _8=E(_4)("img"),_9=E(_1)(_8,E(_0),toJSStr(E(_7)));return _8;}]);});},_a=0,_b=function(_){return _a;},_c=function(_d,_e,_){return new F(function(){return _b(_);});},_f="scroll",_g="submit",_h="blur",_i="focus",_j="change",_k="unload",_l="load",_m=function(_n){switch(E(_n)){case 0:return E(_l);case 1:return E(_k);case 2:return E(_j);case 3:return E(_i);case 4:return E(_h);case 5:return E(_g);default:return E(_f);}},_o=[0,_m,_c],_p="metaKey",_q="shiftKey",_r="altKey",_s="ctrlKey",_t="keyCode",_u=function(_v,_){var _w=_v[E(_t)],_x=_v[E(_s)],_y=_v[E(_r)],_z=_v[E(_q)],_A=_v[E(_p)];return new T(function(){var _B=Number(_w),_C=jsTrunc(_B);return [0,_C,E(_x),E(_y),E(_z),E(_A)];});},_D=function(_E,_F,_){return new F(function(){return _u(E(_F),_);});},_G="keydown",_H="keyup",_I="keypress",_J=function(_K){switch(E(_K)){case 0:return E(_I);case 1:return E(_H);default:return E(_G);}},_L=[0,_J,_D],_M=(function(e){return e.getContext('2d');}),_N=(function(e){return !!e.getContext;}),_O=function(_P,_){return [1,_P];},_Q=function(_R){return E(_R);},_S=[0,_Q,_O],_T=function(_U){return E(E(_U)[1]);},_V=function(_W,_X){return (!B(A(_T,[_Y,_W,_X])))?true:false;},_Z=function(_10,_11){var _12=strEq(E(_10),E(_11));return (E(_12)==0)?false:true;},_13=function(_14,_15){return new F(function(){return _Z(_14,_15);});},_Y=new T(function(){return [0,_13,_V];}),_16=function(_17,_18){var _19=E(_17);return (_19[0]==0)?E(_18):[1,_19[1],new T(function(){return B(_16(_19[2],_18));})];},_1a=new T(function(){return B(unCStr("!!: negative index"));}),_1b=new T(function(){return B(unCStr("Prelude."));}),_1c=new T(function(){return B(_16(_1b,_1a));}),_1d=new T(function(){return B(err(_1c));}),_1e=new T(function(){return B(unCStr("!!: index too large"));}),_1f=new T(function(){return B(_16(_1b,_1e));}),_1g=new T(function(){return B(err(_1f));}),_1h=function(_1i,_1j){while(1){var _1k=E(_1i);if(!_1k[0]){return E(_1g);}else{var _1l=E(_1j);if(!_1l){return E(_1k[1]);}else{_1i=_1k[2];_1j=_1l-1|0;continue;}}}},_1m=function(_1n,_1o){if(_1o>=0){return new F(function(){return _1h(_1n,_1o);});}else{return E(_1d);}},_1p=new T(function(){return B(unCStr(": empty list"));}),_1q=function(_1r){return new F(function(){return err(B(_16(_1b,new T(function(){return B(_16(_1r,_1p));},1))));});},_1s=new T(function(){return B(unCStr("head"));}),_1t=new T(function(){return B(_1q(_1s));}),_1u=function(_1v){var _1w=E(_1v);if(_1w[0]==3){var _1x=E(_1w[1]);if(!_1x[0]){return E(_1t);}else{var _1y=E(_1x[1]);if(!_1y[0]){var _1z=B(_1m(_1x,1));return (_1z[0]==0)?[1,[0,_1y[1],_1z[1]]]:[0];}else{return [0];}}}else{return [0];}},_1A=function(_1B,_1C){var _1D=E(_1C);return (_1D[0]==0)?[0]:[1,new T(function(){return B(A(_1B,[_1D[1]]));}),new T(function(){return B(_1A(_1B,_1D[2]));})];},_1E=function(_1F){var _1G=E(_1F);if(_1G[0]==3){var _1H=B(_1A(_1u,_1G[1]));if(!_1H[0]){return E(_1t);}else{var _1I=E(_1H[1]);if(!_1I[0]){return [0];}else{var _1J=B(_1m(_1H,1));if(!_1J[0]){return [0];}else{var _1K=B(_1m(_1H,2));if(!_1K[0]){return [0];}else{var _1L=B(_1m(_1H,3));return (_1L[0]==0)?[0]:[1,[0,_1I[1],_1J[1],_1K[1],_1L[1]]];}}}}}else{return [0];}},_1M="box",_1N="mouse",_1O="corner",_1P="Dragging",_1Q=[0],_1R=[1,_1Q],_1S="Free",_1T="state",_1U=1,_1V=[1,_1U],_1W=0,_1X=[1,_1W],_1Y=3,_1Z=[1,_1Y],_20=2,_21=[1,_20],_22=new T(function(){return B(unCStr("SW"));}),_23=new T(function(){return B(unCStr("SE"));}),_24=new T(function(){return B(unCStr("NW"));}),_25=new T(function(){return B(unCStr("NE"));}),_26=function(_27,_28){while(1){var _29=E(_27);if(!_29[0]){return (E(_28)[0]==0)?true:false;}else{var _2a=E(_28);if(!_2a[0]){return false;}else{if(E(_29[1])!=E(_2a[1])){return false;}else{_27=_29[2];_28=_2a[2];continue;}}}}},_2b=function(_2c){var _2d=E(_2c);if(_2d[0]==1){var _2e=fromJSStr(_2d[1]);return (!B(_26(_2e,_25)))?(!B(_26(_2e,_24)))?(!B(_26(_2e,_23)))?(!B(_26(_2e,_22)))?[0]:E(_21):E(_1Z):E(_1X):E(_1V);}else{return [0];}},_2f=function(_2g,_2h,_2i){while(1){var _2j=E(_2i);if(!_2j[0]){return [0];}else{var _2k=E(_2j[1]);if(!B(A(_T,[_2g,_2h,_2k[1]]))){_2i=_2j[2];continue;}else{return [1,_2k[2]];}}}},_2l=function(_2m){var _2n=E(_2m);if(_2n[0]==4){var _2o=_2n[1],_2p=B(_2f(_Y,_1T,_2o));if(!_2p[0]){return [0];}else{var _2q=E(_2p[1]);if(_2q[0]==1){var _2r=_2q[1],_2s=strEq(_2r,E(_1S));if(!E(_2s)){var _2t=strEq(_2r,E(_1P));if(!E(_2t)){return [0];}else{var _2u=B(_2f(_Y,_1O,_2o));if(!_2u[0]){return [0];}else{var _2v=B(_2b(_2u[1]));return (_2v[0]==0)?[0]:[1,[1,_2v[1]]];}}}else{return E(_1R);}}else{return [0];}}}else{return [0];}},_2w=function(_2x){var _2y=E(_2x);if(_2y[0]==4){var _2z=_2y[1],_2A=B(_2f(_Y,_1N,_2z));if(!_2A[0]){return [0];}else{var _2B=B(_2l(_2A[1]));if(!_2B[0]){return [0];}else{var _2C=B(_2f(_Y,_1M,_2z));if(!_2C[0]){return [0];}else{var _2D=B(_1E(_2C[1]));return (_2D[0]==0)?[0]:[1,[0,_2B[1],_2D[1]]];}}}}else{return [0];}},_2E=function(_2F){return [0,E(_2F)];},_2G=function(_2H){var _2I=E(_2H);return (_2I[0]==0)?[1,_2I[1]]:[0];},_2J=[0,_2E,_2G],_2K=1,_2L=[1,_2K],_2M=0,_2N=[1,_2M],_2O=new T(function(){return B(unCStr("Top"));}),_2P=new T(function(){return B(unCStr("Bottom"));}),_2Q=function(_2R){var _2S=E(_2R);if(_2S[0]==1){var _2T=fromJSStr(_2S[1]);return (!B(_26(_2T,_2P)))?(!B(_26(_2T,_2O)))?[0]:E(_2N):E(_2L);}else{return [0];}},_2U=1,_2V=[1,_2U],_2W=0,_2X=[1,_2W],_2Y=new T(function(){return B(unCStr("Free"));}),_2Z=new T(function(){return B(unCStr("Dragging"));}),_30=function(_31){var _32=E(_31);if(_32[0]==1){var _33=fromJSStr(_32[1]);return (!B(_26(_33,_2Z)))?(!B(_26(_33,_2Y)))?[0]:E(_2X):E(_2V);}else{return [0];}},_34="title",_35="points",_36=function(_37){var _38=E(_37);if(_38[0]==4){var _39=_38[1],_3a=B(_2f(_Y,_35,_39));if(!_3a[0]){return [0];}else{var _3b=E(_3a[1]);if(_3b[0]==3){var _3c=E(_3b[1]);if(!_3c[0]){return E(_1t);}else{var _3d=E(_3c[1]);if(_3d[0]==3){var _3e=E(_3d[1]);if(!_3e[0]){return E(_1t);}else{var _3f=E(_3e[1]);if(!_3f[0]){var _3g=B(_1m(_3e,1));if(!_3g[0]){var _3h=B(_1m(_3c,1));if(_3h[0]==3){var _3i=E(_3h[1]);if(!_3i[0]){return E(_1t);}else{var _3j=E(_3i[1]);if(!_3j[0]){var _3k=B(_1m(_3i,1));if(!_3k[0]){var _3l=B(_2f(_Y,_34,_39));if(!_3l[0]){return [0];}else{var _3m=E(_3l[1]);return (_3m[0]==1)?[1,[0,[0,_3f[1],_3g[1]],[0,_3j[1],_3k[1]],new T(function(){return fromJSStr(_3m[1]);})]]:[0];}}else{return [0];}}else{return [0];}}}else{return [0];}}else{return [0];}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}},_3n=[0],_3o=function(_3p){var _3q=new T(function(){var _3r=E(E(_3p)[2]);return [3,[1,new T(function(){return B(_2E(_3r[1]));}),[1,new T(function(){return B(_2E(_3r[2]));}),_3n]]];}),_3s=new T(function(){var _3t=E(E(_3p)[1]);return [3,[1,new T(function(){return B(_2E(_3t[1]));}),[1,new T(function(){return B(_2E(_3t[2]));}),_3n]]];});return [1,[0,_34,new T(function(){return [1,toJSStr(E(E(_3p)[3]))];})],[1,[0,_35,[3,[1,_3s,[1,_3q,_3n]]]],_3n]];},_3u=function(_3v){return [4,E(B(_3o(_3v)))];},_3w=[0,_3u,_36],_3x=[1,_3n],_3y=function(_3z){return E(E(_3z)[2]);},_3A=function(_3B,_3C){var _3D=E(_3C);if(_3D[0]==3){var _3E=new T(function(){return B(_3y(_3B));}),_3F=function(_3G){var _3H=E(_3G);if(!_3H[0]){return E(_3x);}else{var _3I=B(A(_3E,[_3H[1]]));if(!_3I[0]){return [0];}else{var _3J=B(_3F(_3H[2]));return (_3J[0]==0)?[0]:[1,[1,_3I[1],_3J[1]]];}}};return new F(function(){return _3F(_3D[1]);});}else{return [0];}},_3K="rotations",_3L=0.1,_3M="step",_3N="choice",_3O="offset",_3P="bottom",_3Q="top",_3R="scans",_3S="mouse",_3T=function(_3U){var _3V=E(_3U);if(_3V[0]==4){var _3W=_3V[1],_3X=B(_2f(_Y,_3S,_3W));if(!_3X[0]){return [0];}else{var _3Y=B(_30(_3X[1]));if(!_3Y[0]){return [0];}else{var _3Z=_3Y[1],_40=B(_2f(_Y,_3R,_3W));if(!_40[0]){return [0];}else{var _41=B(_3A(_3w,_40[1]));if(!_41[0]){return [0];}else{var _42=_41[1],_43=B(_2f(_Y,_3Q,_3W));if(!_43[0]){return [0];}else{var _44=E(_43[1]);if(!_44[0]){var _45=_44[1],_46=B(_2f(_Y,_3P,_3W));if(!_46[0]){return [0];}else{var _47=E(_46[1]);if(!_47[0]){var _48=_47[1],_49=B(_2f(_Y,_3O,_3W));if(!_49[0]){return [0];}else{var _4a=E(_49[1]);if(!_4a[0]){var _4b=_4a[1],_4c=B(_2f(_Y,_3N,_3W));if(!_4c[0]){return [0];}else{var _4d=B(_2Q(_4c[1]));if(!_4d[0]){return [0];}else{var _4e=_4d[1],_4f=B(_2f(_Y,_3M,_3W));if(!_4f[0]){var _4g=B(_2f(_Y,_3K,_3W));if(!_4g[0]){return [0];}else{var _4h=B(_3A(_2J,_4g[1]));return (_4h[0]==0)?[0]:[1,[0,_3Z,_42,_45,_48,_4b,_4e,_3L,_4h[1]]];}}else{var _4i=E(_4f[1]);if(!_4i[0]){var _4j=B(_2f(_Y,_3K,_3W));if(!_4j[0]){return [0];}else{var _4k=B(_3A(_2J,_4j[1]));return (_4k[0]==0)?[0]:[1,[0,_3Z,_42,_45,_48,_4b,_4e,_4i[1],_4k[1]]];}}else{return [0];}}}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}}}}}else{return [0];}},_4l="scans",_4m="calib",_4n=function(_4o){var _4p=E(_4o);if(_4p[0]==4){var _4q=_4p[1],_4r=B(_2f(_Y,_4m,_4q));if(!_4r[0]){return [0];}else{var _4s=B(_2w(_4r[1]));if(!_4s[0]){return [0];}else{var _4t=B(_2f(_Y,_4l,_4q));if(!_4t[0]){return [0];}else{var _4u=B(_3T(_4t[1]));return (_4u[0]==0)?[0]:[1,[0,_4s[1],_4u[1]]];}}}}else{return [0];}},_4v=function(_4w,_4x,_){var _4y=B(A(_4w,[_])),_4z=B(A(_4x,[_]));return _4y;},_4A=function(_4B,_4C,_){var _4D=B(A(_4B,[_])),_4E=B(A(_4C,[_]));return new T(function(){return B(A(_4D,[_4E]));});},_4F=function(_4G,_4H,_){var _4I=B(A(_4H,[_]));return _4G;},_4J=function(_4K,_4L,_){var _4M=B(A(_4L,[_]));return new T(function(){return B(A(_4K,[_4M]));});},_4N=[0,_4J,_4F],_4O=function(_4P,_){return _4P;},_4Q=function(_4R,_4S,_){var _4T=B(A(_4R,[_]));return new F(function(){return A(_4S,[_]);});},_4U=[0,_4N,_4O,_4A,_4Q,_4v],_4V=function(_4W,_4X,_){var _4Y=B(A(_4W,[_]));return new F(function(){return A(_4X,[_4Y,_]);});},_4Z=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_50=new T(function(){return B(unCStr("base"));}),_51=new T(function(){return B(unCStr("IOException"));}),_52=new T(function(){var _53=hs_wordToWord64(4053623282),_54=hs_wordToWord64(3693590983);return [0,_53,_54,[0,_53,_54,_50,_4Z,_51],_3n,_3n];}),_55=function(_56){return E(_52);},_57=function(_58){return E(E(_58)[1]);},_59=function(_5a,_5b,_5c){var _5d=B(A(_5a,[_])),_5e=B(A(_5b,[_])),_5f=hs_eqWord64(_5d[1],_5e[1]);if(!_5f){return [0];}else{var _5g=hs_eqWord64(_5d[2],_5e[2]);return (!_5g)?[0]:[1,_5c];}},_5h=function(_5i){var _5j=E(_5i);return new F(function(){return _59(B(_57(_5j[1])),_55,_5j[2]);});},_5k=new T(function(){return B(unCStr(": "));}),_5l=new T(function(){return B(unCStr(")"));}),_5m=new T(function(){return B(unCStr(" ("));}),_5n=new T(function(){return B(unCStr("interrupted"));}),_5o=new T(function(){return B(unCStr("system error"));}),_5p=new T(function(){return B(unCStr("unsatisified constraints"));}),_5q=new T(function(){return B(unCStr("user error"));}),_5r=new T(function(){return B(unCStr("permission denied"));}),_5s=new T(function(){return B(unCStr("illegal operation"));}),_5t=new T(function(){return B(unCStr("end of file"));}),_5u=new T(function(){return B(unCStr("resource exhausted"));}),_5v=new T(function(){return B(unCStr("resource busy"));}),_5w=new T(function(){return B(unCStr("does not exist"));}),_5x=new T(function(){return B(unCStr("already exists"));}),_5y=new T(function(){return B(unCStr("resource vanished"));}),_5z=new T(function(){return B(unCStr("timeout"));}),_5A=new T(function(){return B(unCStr("unsupported operation"));}),_5B=new T(function(){return B(unCStr("hardware fault"));}),_5C=new T(function(){return B(unCStr("inappropriate type"));}),_5D=new T(function(){return B(unCStr("invalid argument"));}),_5E=new T(function(){return B(unCStr("failed"));}),_5F=new T(function(){return B(unCStr("protocol error"));}),_5G=function(_5H,_5I){switch(E(_5H)){case 0:return new F(function(){return _16(_5x,_5I);});break;case 1:return new F(function(){return _16(_5w,_5I);});break;case 2:return new F(function(){return _16(_5v,_5I);});break;case 3:return new F(function(){return _16(_5u,_5I);});break;case 4:return new F(function(){return _16(_5t,_5I);});break;case 5:return new F(function(){return _16(_5s,_5I);});break;case 6:return new F(function(){return _16(_5r,_5I);});break;case 7:return new F(function(){return _16(_5q,_5I);});break;case 8:return new F(function(){return _16(_5p,_5I);});break;case 9:return new F(function(){return _16(_5o,_5I);});break;case 10:return new F(function(){return _16(_5F,_5I);});break;case 11:return new F(function(){return _16(_5E,_5I);});break;case 12:return new F(function(){return _16(_5D,_5I);});break;case 13:return new F(function(){return _16(_5C,_5I);});break;case 14:return new F(function(){return _16(_5B,_5I);});break;case 15:return new F(function(){return _16(_5A,_5I);});break;case 16:return new F(function(){return _16(_5z,_5I);});break;case 17:return new F(function(){return _16(_5y,_5I);});break;default:return new F(function(){return _16(_5n,_5I);});}},_5J=new T(function(){return B(unCStr("}"));}),_5K=new T(function(){return B(unCStr("{handle: "));}),_5L=function(_5M,_5N,_5O,_5P,_5Q,_5R){var _5S=new T(function(){var _5T=new T(function(){var _5U=new T(function(){var _5V=E(_5P);if(!_5V[0]){return E(_5R);}else{var _5W=new T(function(){return B(_16(_5V,new T(function(){return B(_16(_5l,_5R));},1)));},1);return B(_16(_5m,_5W));}},1);return B(_5G(_5N,_5U));}),_5X=E(_5O);if(!_5X[0]){return E(_5T);}else{return B(_16(_5X,new T(function(){return B(_16(_5k,_5T));},1)));}}),_5Y=E(_5Q);if(!_5Y[0]){var _5Z=E(_5M);if(!_5Z[0]){return E(_5S);}else{var _60=E(_5Z[1]);if(!_60[0]){var _61=new T(function(){var _62=new T(function(){return B(_16(_5J,new T(function(){return B(_16(_5k,_5S));},1)));},1);return B(_16(_60[1],_62));},1);return new F(function(){return _16(_5K,_61);});}else{var _63=new T(function(){var _64=new T(function(){return B(_16(_5J,new T(function(){return B(_16(_5k,_5S));},1)));},1);return B(_16(_60[1],_64));},1);return new F(function(){return _16(_5K,_63);});}}}else{return new F(function(){return _16(_5Y[1],new T(function(){return B(_16(_5k,_5S));},1));});}},_65=function(_66){var _67=E(_66);return new F(function(){return _5L(_67[1],_67[2],_67[3],_67[4],_67[6],_3n);});},_68=function(_69,_6a,_6b){var _6c=E(_6a);return new F(function(){return _5L(_6c[1],_6c[2],_6c[3],_6c[4],_6c[6],_6b);});},_6d=function(_6e,_6f){var _6g=E(_6e);return new F(function(){return _5L(_6g[1],_6g[2],_6g[3],_6g[4],_6g[6],_6f);});},_6h=44,_6i=93,_6j=91,_6k=function(_6l,_6m,_6n){var _6o=E(_6m);if(!_6o[0]){return new F(function(){return unAppCStr("[]",_6n);});}else{var _6p=new T(function(){var _6q=new T(function(){var _6r=function(_6s){var _6t=E(_6s);if(!_6t[0]){return [1,_6i,_6n];}else{var _6u=new T(function(){return B(A(_6l,[_6t[1],new T(function(){return B(_6r(_6t[2]));})]));});return [1,_6h,_6u];}};return B(_6r(_6o[2]));});return B(A(_6l,[_6o[1],_6q]));});return [1,_6j,_6p];}},_6v=function(_6w,_6x){return new F(function(){return _6k(_6d,_6w,_6x);});},_6y=[0,_68,_65,_6v],_6z=new T(function(){return [0,_55,_6y,_6A,_5h,_65];}),_6A=function(_6B){return [0,_6z,_6B];},_6C=[0],_6D=7,_6E=function(_6F){return [0,_6C,_6D,_3n,_6F,_6C,_6C];},_6G=function(_6H,_){var _6I=new T(function(){return B(_6A(new T(function(){return B(_6E(_6H));})));});return new F(function(){return die(_6I);});},_6J=[0,_4U,_4V,_4Q,_4O,_6G],_6K=[0,_6J,_Q],_6L=[0,_6K,_4O],_6M=function(_6N,_6O,_6P,_6Q,_6R,_6S,_6T,_6U){if(_6N!=_6R){return false;}else{if(E(_6O)!=E(_6S)){return false;}else{var _6V=E(_6P),_6W=E(_6T);if(E(_6V[1])!=E(_6W[1])){return false;}else{if(E(_6V[2])!=E(_6W[2])){return false;}else{return new F(function(){return _26(_6Q,_6U);});}}}}},_6X=function(_6Y,_6Z){var _70=E(_6Y),_71=E(_70[1]),_72=E(_6Z),_73=E(_72[1]);return new F(function(){return _6M(E(_71[1]),_71[2],_70[2],_70[3],E(_73[1]),_73[2],_72[2],_72[3]);});},_74="scans",_75=[1,_74,_3n],_76="calib",_77=[1,_76,_75],_78=function(_79){var _7a=E(_79);return [3,[1,new T(function(){return B(_2E(_7a[1]));}),[1,new T(function(){return B(_2E(_7a[2]));}),_3n]]];},_7b=new T(function(){return [1,"Dragging"];}),_7c=[0,_1T,_7b],_7d=new T(function(){return [1,"Free"];}),_7e="state",_7f=[0,_7e,_7d],_7g=[1,_7f,_3n],_7h=[4,E(_7g)],_7i=function(_7j,_7k){switch(E(_7j)){case 0:return new F(function(){return _16(_24,_7k);});break;case 1:return new F(function(){return _16(_25,_7k);});break;case 2:return new F(function(){return _16(_22,_7k);});break;default:return new F(function(){return _16(_23,_7k);});}},_7l=function(_7m){return E(toJSStr(B(_7i(_7m,_3n))));},_7n=function(_7o){return [1,B(_7l(_7o))];},_7p=function(_7q){var _7r=new T(function(){var _7s=E(E(_7q)[2]);return [3,[1,new T(function(){return B(_78(_7s[1]));}),[1,new T(function(){return B(_78(_7s[2]));}),[1,new T(function(){return B(_78(_7s[3]));}),[1,new T(function(){return B(_78(_7s[4]));}),_3n]]]]];}),_7t=new T(function(){var _7u=E(E(_7q)[1]);if(!_7u[0]){return E(_7h);}else{return [4,[1,_7c,[1,[0,_1O,new T(function(){return B(_7n(_7u[1]));})],_3n]]];}});return [1,[0,_1N,_7t],[1,[0,_1M,_7r],_3n]];},_7v="mouse",_7w="scans",_7x="top",_7y="bottom",_7z="offset",_7A="choice",_7B="step",_7C="rotations",_7D=[1,_7C,_3n],_7E=[1,_7B,_7D],_7F=[1,_7A,_7E],_7G=[1,_7z,_7F],_7H=[1,_7y,_7G],_7I=[1,_7x,_7H],_7J=[1,_7w,_7I],_7K=[1,_7v,_7J],_7L=function(_7M,_7N){var _7O=E(_7M);if(!_7O[0]){return [0];}else{var _7P=E(_7N);return (_7P[0]==0)?[0]:[1,[0,_7O[1],_7P[1]],new T(function(){return B(_7L(_7O[2],_7P[2]));})];}},_7Q=function(_7R){return new F(function(){return _7L(_7K,[1,new T(function(){if(!E(E(_7R)[1])){return [1,toJSStr(E(_2Y))];}else{return [1,toJSStr(E(_2Z))];}}),[1,new T(function(){return [3,E(B(_1A(_3u,E(_7R)[2])))];}),[1,new T(function(){return [0,E(E(_7R)[3])];}),[1,new T(function(){return [0,E(E(_7R)[4])];}),[1,new T(function(){return [0,E(E(_7R)[5])];}),[1,new T(function(){if(!E(E(_7R)[6])){return [1,toJSStr(E(_2O))];}else{return [1,toJSStr(E(_2P))];}}),[1,new T(function(){return [0,E(E(_7R)[7])];}),[1,new T(function(){return [3,E(B(_1A(_2E,E(_7R)[8])))];}),_3n]]]]]]]]);});},_7S=function(_7T){return [1,E(_7T)];},_7U="deltaZ",_7V="deltaY",_7W="deltaX",_7X=function(_7Y,_7Z){var _80=jsShowI(_7Y);return new F(function(){return _16(fromJSStr(_80),_7Z);});},_81=41,_82=40,_83=function(_84,_85,_86){if(_85>=0){return new F(function(){return _7X(_85,_86);});}else{if(_84<=6){return new F(function(){return _7X(_85,_86);});}else{return [1,_82,new T(function(){var _87=jsShowI(_85);return B(_16(fromJSStr(_87),[1,_81,_86]));})];}}},_88=new T(function(){return B(unCStr(")"));}),_89=new T(function(){return B(_83(0,2,_88));}),_8a=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_89));}),_8b=function(_8c){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_83(0,_8c,_8a));}))));});},_8d=function(_8e,_){return new T(function(){var _8f=Number(E(_8e)),_8g=jsTrunc(_8f);if(_8g<0){return B(_8b(_8g));}else{if(_8g>2){return B(_8b(_8g));}else{return _8g;}}});},_8h=0,_8i=[0,_8h,_8h,_8h],_8j="button",_8k=new T(function(){return jsGetMouseCoords;}),_8l=function(_8m,_){var _8n=E(_8m);if(!_8n[0]){return _3n;}else{var _8o=B(_8l(_8n[2],_));return [1,new T(function(){var _8p=Number(E(_8n[1]));return jsTrunc(_8p);}),_8o];}},_8q=function(_8r,_){var _8s=__arr2lst(0,_8r);return new F(function(){return _8l(_8s,_);});},_8t=function(_8u,_){return new F(function(){return _8q(E(_8u),_);});},_8v=function(_8w,_){return new T(function(){var _8x=Number(E(_8w));return jsTrunc(_8x);});},_8y=[0,_8v,_8t],_8z=function(_8A,_){var _8B=E(_8A);if(!_8B[0]){return _3n;}else{var _8C=B(_8z(_8B[2],_));return [1,_8B[1],_8C];}},_8D=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_8E=[0,_6C,_6D,_3n,_8D,_6C,_6C],_8F=new T(function(){return B(_6A(_8E));}),_8G=function(_){return new F(function(){return die(_8F);});},_8H=function(_8I){return E(E(_8I)[1]);},_8J=function(_8K,_8L,_8M,_){var _8N=__arr2lst(0,_8M),_8O=B(_8z(_8N,_)),_8P=E(_8O);if(!_8P[0]){return new F(function(){return _8G(_);});}else{var _8Q=E(_8P[2]);if(!_8Q[0]){return new F(function(){return _8G(_);});}else{if(!E(_8Q[2])[0]){var _8R=B(A(_8H,[_8K,_8P[1],_])),_8S=B(A(_8H,[_8L,_8Q[1],_]));return [0,_8R,_8S];}else{return new F(function(){return _8G(_);});}}}},_8T=function(_){return new F(function(){return __jsNull();});},_8U=function(_8V){var _8W=B(A(_8V,[_]));return E(_8W);},_8X=new T(function(){return B(_8U(_8T));}),_8Y=new T(function(){return E(_8X);}),_8Z=function(_90,_91,_){if(E(_90)==7){var _92=E(_8k)(_91),_93=B(_8J(_8y,_8y,_92,_)),_94=_91[E(_7W)],_95=_91[E(_7V)],_96=_91[E(_7U)];return new T(function(){return [0,E(_93),E(_6C),[0,_94,_95,_96]];});}else{var _97=E(_8k)(_91),_98=B(_8J(_8y,_8y,_97,_)),_99=_91[E(_8j)],_9a=__eq(_99,E(_8Y));if(!E(_9a)){var _9b=B(_8d(_99,_));return new T(function(){return [0,E(_98),[1,_9b],E(_8i)];});}else{return new T(function(){return [0,E(_98),E(_6C),E(_8i)];});}}},_9c=function(_9d,_9e,_){return new F(function(){return _8Z(_9d,E(_9e),_);});},_9f="mouseout",_9g="mouseover",_9h="mousemove",_9i="mouseup",_9j="mousedown",_9k="dblclick",_9l="click",_9m="wheel",_9n=function(_9o){switch(E(_9o)){case 0:return E(_9l);case 1:return E(_9k);case 2:return E(_9j);case 3:return E(_9i);case 4:return E(_9h);case 5:return E(_9g);case 6:return E(_9f);default:return E(_9m);}},_9p=[0,_9n,_9c],_9q=function(_){return new F(function(){return E(_4)("td");});},_9r=function(_9s){return E(E(_9s)[1]);},_9t=function(_9u){return E(E(_9u)[3]);},_9v=function(_9w){return E(E(_9w)[2]);},_9x=function(_9y){return E(E(_9y)[4]);},_9z=(function(c,p){p.appendChild(c);}),_9A=function(_9B){return E(E(_9B)[1]);},_9C=(function(e,p,v){e.setAttribute(p, v);}),_9D=(function(e,p,v){e.style[p] = v;}),_9E=function(_9F,_9G,_9H,_9I){var _9J=new T(function(){return B(A(_9A,[_9F,_9H]));}),_9K=function(_9L,_){var _9M=E(_9L);if(!_9M[0]){return _a;}else{var _9N=E(_9J),_9O=E(_9z),_9P=_9O(E(_9M[1]),_9N),_9Q=_9M[2];while(1){var _9R=E(_9Q);if(!_9R[0]){return _a;}else{var _9S=_9O(E(_9R[1]),_9N);_9Q=_9R[2];continue;}}}},_9T=function(_9U,_){while(1){var _9V=B((function(_9W,_){var _9X=E(_9W);if(!_9X[0]){return _a;}else{var _9Y=_9X[2],_9Z=E(_9X[1]);if(!_9Z[0]){var _a0=_9Z[2],_a1=E(_9Z[1]);switch(_a1[0]){case 0:var _a2=E(_9J),_a3=E(_1),_a4=_a3(_a2,_a1[1],_a0),_a5=_9Y;while(1){var _a6=E(_a5);if(!_a6[0]){return _a;}else{var _a7=_a6[2],_a8=E(_a6[1]);if(!_a8[0]){var _a9=_a8[2],_aa=E(_a8[1]);switch(_aa[0]){case 0:var _ab=_a3(_a2,_aa[1],_a9);_a5=_a7;continue;case 1:var _ac=E(_9D)(_a2,_aa[1],_a9);_a5=_a7;continue;default:var _ad=E(_9C)(_a2,_aa[1],_a9);_a5=_a7;continue;}}else{var _ae=B(_9K(_a8[1],_));_a5=_a7;continue;}}}break;case 1:var _af=E(_9J),_ag=E(_9D),_ah=_ag(_af,_a1[1],_a0),_ai=_9Y;while(1){var _aj=E(_ai);if(!_aj[0]){return _a;}else{var _ak=_aj[2],_al=E(_aj[1]);if(!_al[0]){var _am=_al[2],_an=E(_al[1]);switch(_an[0]){case 0:var _ao=E(_1)(_af,_an[1],_am);_ai=_ak;continue;case 1:var _ap=_ag(_af,_an[1],_am);_ai=_ak;continue;default:var _aq=E(_9C)(_af,_an[1],_am);_ai=_ak;continue;}}else{var _ar=B(_9K(_al[1],_));_ai=_ak;continue;}}}break;default:var _as=E(_9J),_at=E(_9C),_au=_at(_as,_a1[1],_a0),_av=_9Y;while(1){var _aw=E(_av);if(!_aw[0]){return _a;}else{var _ax=_aw[2],_ay=E(_aw[1]);if(!_ay[0]){var _az=_ay[2],_aA=E(_ay[1]);switch(_aA[0]){case 0:var _aB=E(_1)(_as,_aA[1],_az);_av=_ax;continue;case 1:var _aC=E(_9D)(_as,_aA[1],_az);_av=_ax;continue;default:var _aD=_at(_as,_aA[1],_az);_av=_ax;continue;}}else{var _aE=B(_9K(_ay[1],_));_av=_ax;continue;}}}}}else{var _aF=B(_9K(_9Z[1],_));_9U=_9Y;return null;}}})(_9U,_));if(_9V!=null){return _9V;}}};return new F(function(){return A(_2,[_9G,function(_){return new F(function(){return _9T(_9I,_);});}]);});},_aG=function(_aH,_aI,_aJ,_aK){var _aL=B(_9r(_aI)),_aM=function(_aN){return new F(function(){return A(_9t,[_aL,new T(function(){return B(_9E(_aH,_aI,_aN,_aK));}),new T(function(){return B(A(_9x,[_aL,_aN]));})]);});};return new F(function(){return A(_9v,[_aL,_aJ,_aM]);});},_aO=function(_aP,_){var _aQ=E(_aP);if(!_aQ[0]){return _3n;}else{var _aR=B(A(_aG,[_S,_6K,_9q,[1,[1,[1,_aQ[1],_3n]],_3n],_])),_aS=B(_aO(_aQ[2],_));return [1,_aR,_aS];}},_aT=function(_aU,_aV,_){var _aW=B(A(_aG,[_S,_6K,_9q,[1,[1,[1,_aU,_3n]],_3n],_])),_aX=B(_aO(_aV,_));return [1,_aW,_aX];},_aY=(function(s){return document.createTextNode(s);}),_aZ=function(_b0,_){var _b1=jsShow(_b0),_b2=E(_aY)(toJSStr(fromJSStr(_b1)));return new F(function(){return A(_aG,[_S,_6K,_9q,[1,[1,[1,_b2,_3n]],_3n],_]);});},_b3=function(_b4,_b5,_b6){var _b7=(_b6-_b5)*25/900;if(!_b7){var _b8=rintDouble(0/_b4);return _b8&4294967295;}else{if(_b7<=0){var _b9=rintDouble( -_b7/_b4);return _b9&4294967295;}else{var _ba=rintDouble(_b7/_b4);return _ba&4294967295;}}},_bb=function(_bc,_bd){while(1){var _be=E(_bc);if(!_be[0]){return E(_bd);}else{var _bf=_bd+1|0;_bc=_be[2];_bd=_bf;continue;}}},_bg=function(_bh,_bi){return [0,E(_bh),toJSStr(E(_bi))];},_bj=2,_bk=0,_bl=new T(function(){return B(unCStr("x1"));}),_bm=new T(function(){return B(unCStr("y1"));}),_bn=new T(function(){return B(unCStr("x2"));}),_bo=new T(function(){return B(unCStr("y2"));}),_bp=new T(function(){return B(unCStr("frames"));}),_bq=new T(function(){return B(unCStr("time (minutes)"));}),_br=new T(function(){return B(unCStr("title"));}),_bs=new T(function(){return B(unCStr("Delete"));}),_bt=[1,_bs,_3n],_bu=[1,_br,_bt],_bv=[1,_bq,_bu],_bw=[1,_bp,_bv],_bx=[1,_bo,_bw],_by=[1,_bn,_bx],_bz=function(_){return new F(function(){return E(_4)("span");});},_bA=new T(function(){return [0,[2,"class"],"glyphicon glyphicon-remove"];}),_bB=[1,_bA,_3n],_bC=new T(function(){return B(_aG(_S,_6K,_bz,_bB));}),_bD=function(_){return new F(function(){return E(_4)("input");});},_bE=function(_){return new F(function(){return E(_4)("tr");});},_bF=function(_){return new F(function(){return E(_4)("th");});},_bG=function(_){return new F(function(){return E(_4)("button");});},_bH=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_bI=function(_bJ){var _bK=I_decodeDouble(_bJ);return [0,[1,_bK[2]],_bK[1]];},_bL=function(_bM){var _bN=E(_bM);if(!_bN[0]){return _bN[1];}else{return new F(function(){return I_toNumber(_bN[1]);});}},_bO=function(_bP){return [0,_bP];},_bQ=function(_bR){var _bS=hs_intToInt64(2147483647),_bT=hs_leInt64(_bR,_bS);if(!_bT){return [1,I_fromInt64(_bR)];}else{var _bU=hs_intToInt64(-2147483648),_bV=hs_geInt64(_bR,_bU);if(!_bV){return [1,I_fromInt64(_bR)];}else{var _bW=hs_int64ToInt(_bR);return new F(function(){return _bO(_bW);});}}},_bX=function(_bY){var _bZ=hs_intToInt64(_bY);return E(_bZ);},_c0=function(_c1){var _c2=E(_c1);if(!_c2[0]){return new F(function(){return _bX(_c2[1]);});}else{return new F(function(){return I_toInt64(_c2[1]);});}},_c3=new T(function(){return [2,"value"];}),_c4=new T(function(){return [0,[2,"type"],"text"];}),_c5=new T(function(){return [0,[2,"class"],"btn btn-danger"];}),_c6=function(_c7){return E(E(_c7)[1]);},_c8=function(_c9){return E(E(_c9)[2]);},_ca=function(_cb){return E(E(_cb)[1]);},_cc=function(_){return new F(function(){return nMV(_6C);});},_cd=new T(function(){return B(_8U(_cc));}),_ce=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_cf=function(_cg){return E(E(_cg)[2]);},_ch=function(_ci,_cj,_ck,_cl,_cm,_cn){var _co=B(_c6(_ci)),_cp=B(_9r(_co)),_cq=new T(function(){return B(_2(_co));}),_cr=new T(function(){return B(_9x(_cp));}),_cs=new T(function(){return B(A(_9A,[_cj,_cl]));}),_ct=new T(function(){return B(A(_ca,[_ck,_cm]));}),_cu=function(_cv){return new F(function(){return A(_cr,[[0,_ct,_cs,_cv]]);});},_cw=function(_cx){var _cy=new T(function(){var _cz=new T(function(){var _cA=__createJSFunc(2,function(_cB,_){var _cC=B(A(E(_cx),[_cB,_]));return _8Y;}),_cD=_cA;return function(_){return new F(function(){return E(_ce)(E(_cs),E(_ct),_cD);});};});return B(A(_cq,[_cz]));});return new F(function(){return A(_9v,[_cp,_cy,_cu]);});},_cE=new T(function(){var _cF=new T(function(){return B(_2(_co));}),_cG=function(_cH){var _cI=new T(function(){return B(A(_cF,[function(_){var _=wMV(E(_cd),[1,_cH]);return new F(function(){return A(_c8,[_ck,_cm,_cH,_]);});}]));});return new F(function(){return A(_9v,[_cp,_cI,_cn]);});};return B(A(_cf,[_ci,_cG]));});return new F(function(){return A(_9v,[_cp,_cE,_cw]);});},_cJ=function(_cK,_cL){while(1){var _cM=E(_cK);if(!_cM[0]){return E(_cL);}else{var _cN=[1,_cM[1],_cL];_cK=_cM[2];_cL=_cN;continue;}}},_cO=function(_cP,_cQ){while(1){var _cR=E(_cP);if(!_cR[0]){_cP=[1,I_fromInt(_cR[1])];continue;}else{return [1,I_shiftLeft(_cR[1],_cQ)];}}},_cS=function(_cT,_cU,_cV,_cW,_){var _cX=E(_bH)(_cW),_cY=E(_aY),_cZ=_cY(toJSStr(E(_bl))),_d0=B(A(_aG,[_S,_6K,_bF,[1,[1,[1,_cZ,_3n]],_3n],_])),_d1=function(_d2,_){var _d3=E(_d2);if(!_d3[0]){return _3n;}else{var _d4=_cY(toJSStr(E(_d3[1]))),_d5=B(A(_aG,[_S,_6K,_bF,[1,[1,[1,_d4,_3n]],_3n],_])),_d6=B(_d1(_d3[2],_));return [1,_d5,_d6];}},_d7=B((function(_d8,_d9,_){var _da=_cY(toJSStr(E(_d8))),_db=B(A(_aG,[_S,_6K,_bF,[1,[1,[1,_da,_3n]],_3n],_])),_dc=B(_d1(_d9,_));return [1,_db,_dc];})(_bm,_by,_)),_dd=B(A(_aG,[_S,_6K,_bE,[1,[1,[1,_d0,_d7]],_3n],_])),_de=E(_9z),_df=_de(E(_dd),_cW),_dg=E(_cV),_dh=_dg[8],_di=B(_cJ(_dg[2],_3n));if(!_di[0]){return _a;}else{var _dj=E(_di[1]),_dk=E(_dj[1]),_dl=E(_dj[2]),_dm=E(_dk[1]),_dn=B(_aZ(_dm*25/900,_)),_do=_dn,_dp=E(_dk[2]),_dq=B(_aZ(_dp*25/900,_)),_dr=_dq,_ds=E(_dl[1]),_dt=B(_aZ(_ds*25/900,_)),_du=_dt,_dv=E(_dl[2]),_dw=B(_aZ(_dv*25/900,_)),_dx=_dw,_dy=E(_dg[7]),_dz=function(_dA){var _dB=B(_aZ(_dA,_)),_dC=_dB,_dD=function(_dE){var _dF=rintDouble(_dE*5.8333333333333334e-2*B(_bb(_dh,0))),_dG=B(_bI(_dF)),_dH=_dG[1],_dI=_dG[2],_dJ=function(_dK){var _dL=B(_aZ(_dK,_)),_dM=B(_aT(_do,[1,_dr,[1,_du,[1,_dx,[1,_dC,[1,_dL,_3n]]]]],_)),_dN=B(A(_aG,[_S,_6K,_bE,[1,new T(function(){return B(_7S(_dM));}),_3n],_])),_dO=B(A(_aG,[_S,_6K,_bD,[1,_c4,[1,new T(function(){return B(_bg(_c3,_dj[3]));}),_3n]],_])),_dP=B(A(_bC,[_])),_dQ=B(A(_aG,[_S,_6K,_bG,[1,_c5,[1,[1,[1,_dP,_3n]],_3n]],_])),_dR=B(A(_aG,[_S,_6K,_9q,[1,[1,[1,_dO,_3n]],_3n],_])),_dS=E(_dN),_dT=_de(E(_dR),_dS),_dU=E(_dQ),_dV=_de(_dU,_dS),_dW=new T(function(){return B(A(_cU,[_dj]));}),_dX=B(A(_ch,[_6L,_S,_9p,_dU,_bk,function(_dY){return E(_dW);},_])),_dZ=new T(function(){return B(A(_cT,[_dO,_dj]));}),_e0=B(A(_ch,[_6L,_S,_o,_dO,_bj,function(_e1){return E(_dZ);},_])),_e2=_de(_dS,_cW),_e3=function(_e4,_){var _e5=E(_e4);if(!_e5[0]){return _3n;}else{var _e6=E(_e5[1]),_e7=E(_e6[1]),_e8=E(_e6[2]),_e9=E(_e7[1]),_ea=B(_aZ(_e9*25/900,_)),_eb=_ea,_ec=E(_e7[2]),_ed=B(_aZ(_ec*25/900,_)),_ee=_ed,_ef=E(_e8[1]),_eg=B(_aZ(_ef*25/900,_)),_eh=_eg,_ei=E(_e8[2]),_ej=B(_aZ(_ei*25/900,_)),_ek=_ej,_el=function(_em){var _en=B(_aZ(_em,_)),_eo=_en,_ep=function(_eq){var _er=rintDouble(_eq*5.8333333333333334e-2*B(_bb(_dh,0))),_es=B(_bI(_er)),_et=_es[1],_eu=_es[2],_ev=function(_ew){var _ex=B(_aZ(_ew,_)),_ey=B(_aT(_eb,[1,_ee,[1,_eh,[1,_ek,[1,_eo,[1,_ex,_3n]]]]],_)),_ez=B(A(_aG,[_S,_6K,_bE,[1,new T(function(){return B(_7S(_ey));}),_3n],_])),_eA=B(A(_aG,[_S,_6K,_bD,[1,_c4,[1,new T(function(){return B(_bg(_c3,_e6[3]));}),_3n]],_])),_eB=B(A(_bC,[_])),_eC=B(A(_aG,[_S,_6K,_bG,[1,_c5,[1,[1,[1,_eB,_3n]],_3n]],_])),_eD=B(A(_aG,[_S,_6K,_9q,[1,[1,[1,_eA,_3n]],_3n],_])),_eE=E(_ez),_eF=_de(E(_eD),_eE),_eG=E(_eC),_eH=_de(_eG,_eE),_eI=new T(function(){return B(A(_cU,[_e6]));}),_eJ=B(A(_ch,[_6L,_S,_9p,_eG,_bk,function(_eK){return E(_eI);},_])),_eL=new T(function(){return B(A(_cT,[_eA,_e6]));}),_eM=B(A(_ch,[_6L,_S,_o,_eA,_bj,function(_eN){return E(_eL);},_])),_eO=_de(_eE,_cW),_eP=B(_e3(_e5[2],_));return [1,_a,_eP];};if(_eu>=0){return new F(function(){return _ev(B(_bL(B(_cO(_et,_eu)))));});}else{var _eQ=hs_uncheckedIShiftRA64(B(_c0(_et)), -_eu);return new F(function(){return _ev(B(_bL(B(_bQ(_eQ)))));});}};if(_e9!=_ef){return new F(function(){return _ep(B(_b3(_dy,_e9,_ef)));});}else{return new F(function(){return _ep(B(_b3(_dy,_ec,_ei)));});}};if(_e9!=_ef){return new F(function(){return _el(B(_b3(_dy,_e9,_ef)));});}else{return new F(function(){return _el(B(_b3(_dy,_ec,_ei)));});}}},_eR=B(_e3(_di[2],_));return [1,_a,_eR];};if(_dI>=0){return new F(function(){return _dJ(B(_bL(B(_cO(_dH,_dI)))));});}else{var _eS=hs_uncheckedIShiftRA64(B(_c0(_dH)), -_dI);return new F(function(){return _dJ(B(_bL(B(_bQ(_eS)))));});}};if(_dm!=_ds){return new F(function(){return _dD(B(_b3(_dy,_dm,_ds)));});}else{return new F(function(){return _dD(B(_b3(_dy,_dp,_dv)));});}};if(_dm!=_ds){var _eT=B(_dz(B(_b3(_dy,_dm,_ds))));return _a;}else{var _eU=B(_dz(B(_b3(_dy,_dp,_dv))));return _a;}}},_eV=function(_){return _a;},_eW=(function(ctx){ctx.restore();}),_eX=(function(ctx){ctx.save();}),_eY=(function(ctx,x,y){ctx.scale(x,y);}),_eZ=function(_f0,_f1,_f2,_f3,_){var _f4=E(_eX)(_f3),_f5=E(_eY)(_f3,E(_f0),E(_f1)),_f6=B(A(_f2,[_f3,_])),_f7=E(_eW)(_f3);return new F(function(){return _eV(_);});},_f8=(function(ctx){ctx.beginPath();}),_f9=(function(ctx){ctx.stroke();}),_fa=function(_fb,_fc,_){var _fd=E(_f8)(_fc),_fe=B(A(_fb,[_fc,_])),_ff=E(_f9)(_fc);return new F(function(){return _eV(_);});},_fg=(function(ctx,i,x,y){ctx.drawImage(i,x,y);}),_fh=function(_fi,_fj,_fk,_fl,_){var _fm=E(_fg)(_fl,_fi,_fj,_fk);return new F(function(){return _eV(_);});},_fn=",",_fo="[",_fp="]",_fq="{",_fr="}",_fs=":",_ft="\"",_fu="true",_fv="false",_fw="null",_fx=new T(function(){return JSON.stringify;}),_fy=function(_fz,_fA){var _fB=E(_fA);switch(_fB[0]){case 0:return [0,new T(function(){return jsShow(_fB[1]);}),_fz];case 1:return [0,new T(function(){var _fC=E(_fx)(_fB[1]);return String(_fC);}),_fz];case 2:return (!E(_fB[1]))?[0,_fv,_fz]:[0,_fu,_fz];case 3:var _fD=E(_fB[1]);if(!_fD[0]){return [0,_fo,[1,_fp,_fz]];}else{var _fE=new T(function(){var _fF=new T(function(){var _fG=function(_fH){var _fI=E(_fH);if(!_fI[0]){return [1,_fp,_fz];}else{var _fJ=new T(function(){var _fK=B(_fy(new T(function(){return B(_fG(_fI[2]));}),_fI[1]));return [1,_fK[1],_fK[2]];});return [1,_fn,_fJ];}};return B(_fG(_fD[2]));}),_fL=B(_fy(_fF,_fD[1]));return [1,_fL[1],_fL[2]];});return [0,_fo,_fE];}break;case 4:var _fM=E(_fB[1]);if(!_fM[0]){return [0,_fq,[1,_fr,_fz]];}else{var _fN=E(_fM[1]),_fO=new T(function(){var _fP=new T(function(){var _fQ=function(_fR){var _fS=E(_fR);if(!_fS[0]){return [1,_fr,_fz];}else{var _fT=E(_fS[1]),_fU=new T(function(){var _fV=B(_fy(new T(function(){return B(_fQ(_fS[2]));}),_fT[2]));return [1,_fV[1],_fV[2]];});return [1,_fn,[1,_ft,[1,_fT[1],[1,_ft,[1,_fs,_fU]]]]];}};return B(_fQ(_fM[2]));}),_fW=B(_fy(_fP,_fN[2]));return [1,_fW[1],_fW[2]];});return [0,_fq,[1,new T(function(){var _fX=E(_fx)(E(_fN[1]));return String(_fX);}),[1,_fs,_fO]]];}break;default:return [0,_fw,_fz];}},_fY=new T(function(){return toJSStr(_3n);}),_fZ=function(_g0){var _g1=B(_fy(_3n,_g0)),_g2=jsCat([1,_g1[1],_g1[2]],E(_fY));return E(_g2);},_g3=function(_g4){while(1){var _g5=E(_g4);if(!_g5[0]){_g4=[1,I_fromInt(_g5[1])];continue;}else{return new F(function(){return I_toString(_g5[1]);});}}},_g6=function(_g7,_g8){return new F(function(){return _16(fromJSStr(B(_g3(_g7))),_g8);});},_g9=function(_ga,_gb){var _gc=E(_ga);if(!_gc[0]){var _gd=_gc[1],_ge=E(_gb);return (_ge[0]==0)?_gd<_ge[1]:I_compareInt(_ge[1],_gd)>0;}else{var _gf=_gc[1],_gg=E(_gb);return (_gg[0]==0)?I_compareInt(_gf,_gg[1])<0:I_compare(_gf,_gg[1])<0;}},_gh=[0,0],_gi=function(_gj,_gk,_gl){if(_gj<=6){return new F(function(){return _g6(_gk,_gl);});}else{if(!B(_g9(_gk,_gh))){return new F(function(){return _g6(_gk,_gl);});}else{return [1,_82,new T(function(){return B(_16(fromJSStr(B(_g3(_gk))),[1,_81,_gl]));})];}}},_gm=0,_gn=1,_go=function(_gp){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_gp));}))));});},_gq=new T(function(){return B(_go("ww_suPF MouseState"));}),_gr=function(_gs){var _gt=E(_gs);if(!_gt[0]){return [0];}else{return new F(function(){return _16(_gt[1],new T(function(){return B(_gr(_gt[2]));},1));});}},_gu=new T(function(){return B(unCStr("\r\n"));}),_gv=new T(function(){return B(_16(_gu,_gu));}),_gw=function(_gx,_gy){var _gz=E(_gy);return (_gz[0]==0)?[0]:[1,_gx,[1,_gz[1],new T(function(){return B(_gw(_gx,_gz[2]));})]];},_gA=new T(function(){return B(unCStr("printf: formatting string ended prematurely"));}),_gB=new T(function(){return B(err(_gA));}),_gC=function(_gD,_gE){var _gF=E(_gE);return (_gF[0]==0)?E(_gB):[0,_3n,_gF[1],_gF[2]];},_gG=new T(function(){return B(unCStr("ACK"));}),_gH=new T(function(){return B(unCStr("BEL"));}),_gI=new T(function(){return B(unCStr("BS"));}),_gJ=new T(function(){return B(unCStr("SP"));}),_gK=[1,_gJ,_3n],_gL=new T(function(){return B(unCStr("US"));}),_gM=[1,_gL,_gK],_gN=new T(function(){return B(unCStr("RS"));}),_gO=[1,_gN,_gM],_gP=new T(function(){return B(unCStr("GS"));}),_gQ=[1,_gP,_gO],_gR=new T(function(){return B(unCStr("FS"));}),_gS=[1,_gR,_gQ],_gT=new T(function(){return B(unCStr("ESC"));}),_gU=[1,_gT,_gS],_gV=new T(function(){return B(unCStr("SUB"));}),_gW=[1,_gV,_gU],_gX=new T(function(){return B(unCStr("EM"));}),_gY=[1,_gX,_gW],_gZ=new T(function(){return B(unCStr("CAN"));}),_h0=[1,_gZ,_gY],_h1=new T(function(){return B(unCStr("ETB"));}),_h2=[1,_h1,_h0],_h3=new T(function(){return B(unCStr("SYN"));}),_h4=[1,_h3,_h2],_h5=new T(function(){return B(unCStr("NAK"));}),_h6=[1,_h5,_h4],_h7=new T(function(){return B(unCStr("DC4"));}),_h8=[1,_h7,_h6],_h9=new T(function(){return B(unCStr("DC3"));}),_ha=[1,_h9,_h8],_hb=new T(function(){return B(unCStr("DC2"));}),_hc=[1,_hb,_ha],_hd=new T(function(){return B(unCStr("DC1"));}),_he=[1,_hd,_hc],_hf=new T(function(){return B(unCStr("DLE"));}),_hg=[1,_hf,_he],_hh=new T(function(){return B(unCStr("SI"));}),_hi=[1,_hh,_hg],_hj=new T(function(){return B(unCStr("SO"));}),_hk=[1,_hj,_hi],_hl=new T(function(){return B(unCStr("CR"));}),_hm=[1,_hl,_hk],_hn=new T(function(){return B(unCStr("FF"));}),_ho=[1,_hn,_hm],_hp=new T(function(){return B(unCStr("VT"));}),_hq=[1,_hp,_ho],_hr=new T(function(){return B(unCStr("LF"));}),_hs=[1,_hr,_hq],_ht=new T(function(){return B(unCStr("HT"));}),_hu=[1,_ht,_hs],_hv=[1,_gI,_hu],_hw=[1,_gH,_hv],_hx=[1,_gG,_hw],_hy=new T(function(){return B(unCStr("ENQ"));}),_hz=[1,_hy,_hx],_hA=new T(function(){return B(unCStr("EOT"));}),_hB=[1,_hA,_hz],_hC=new T(function(){return B(unCStr("ETX"));}),_hD=[1,_hC,_hB],_hE=new T(function(){return B(unCStr("STX"));}),_hF=[1,_hE,_hD],_hG=new T(function(){return B(unCStr("SOH"));}),_hH=[1,_hG,_hF],_hI=new T(function(){return B(unCStr("NUL"));}),_hJ=[1,_hI,_hH],_hK=92,_hL=new T(function(){return B(unCStr("\\DEL"));}),_hM=new T(function(){return B(unCStr("\\a"));}),_hN=new T(function(){return B(unCStr("\\\\"));}),_hO=new T(function(){return B(unCStr("\\SO"));}),_hP=new T(function(){return B(unCStr("\\r"));}),_hQ=new T(function(){return B(unCStr("\\f"));}),_hR=new T(function(){return B(unCStr("\\v"));}),_hS=new T(function(){return B(unCStr("\\n"));}),_hT=new T(function(){return B(unCStr("\\t"));}),_hU=new T(function(){return B(unCStr("\\b"));}),_hV=function(_hW,_hX){if(_hW<=127){var _hY=E(_hW);switch(_hY){case 92:return new F(function(){return _16(_hN,_hX);});break;case 127:return new F(function(){return _16(_hL,_hX);});break;default:if(_hY<32){var _hZ=E(_hY);switch(_hZ){case 7:return new F(function(){return _16(_hM,_hX);});break;case 8:return new F(function(){return _16(_hU,_hX);});break;case 9:return new F(function(){return _16(_hT,_hX);});break;case 10:return new F(function(){return _16(_hS,_hX);});break;case 11:return new F(function(){return _16(_hR,_hX);});break;case 12:return new F(function(){return _16(_hQ,_hX);});break;case 13:return new F(function(){return _16(_hP,_hX);});break;case 14:return new F(function(){return _16(_hO,new T(function(){var _i0=E(_hX);if(!_i0[0]){return [0];}else{if(E(_i0[1])==72){return B(unAppCStr("\\&",_i0));}else{return E(_i0);}}},1));});break;default:return new F(function(){return _16([1,_hK,new T(function(){return B(_1m(_hJ,_hZ));})],_hX);});}}else{return [1,_hY,_hX];}}}else{var _i1=new T(function(){var _i2=jsShowI(_hW);return B(_16(fromJSStr(_i2),new T(function(){var _i3=E(_hX);if(!_i3[0]){return [0];}else{var _i4=E(_i3[1]);if(_i4<48){return E(_i3);}else{if(_i4>57){return E(_i3);}else{return B(unAppCStr("\\&",_i3));}}}},1)));});return [1,_hK,_i1];}},_i5=39,_i6=[1,_i5,_3n],_i7=new T(function(){return B(unCStr("\'\\\'\'"));}),_i8=new T(function(){return B(_16(_i7,_3n));}),_i9=function(_ia){var _ib=new T(function(){var _ic=new T(function(){var _id=E(_ia);if(_id==39){return E(_i8);}else{return [1,_i5,new T(function(){return B(_hV(_id,_i6));})];}});return B(unAppCStr("bad formatting char ",_ic));});return new F(function(){return err(B(unAppCStr("printf: ",_ib)));});},_ie=new T(function(){return B(unCStr("-"));}),_if=new T(function(){return B(unCStr("printf: internal error: impossible dfmt"));}),_ig=new T(function(){return B(err(_if));}),_ih=function(_ii){var _ij=E(_ii);return new F(function(){return Math.log(_ij+(_ij+1)*Math.sqrt((_ij-1)/(_ij+1)));});},_ik=function(_il){var _im=E(_il);return new F(function(){return Math.log(_im+Math.sqrt(1+_im*_im));});},_in=function(_io){var _ip=E(_io);return 0.5*Math.log((1+_ip)/(1-_ip));},_iq=function(_ir,_is){return Math.log(E(_is))/Math.log(E(_ir));},_it=3.141592653589793,_iu=[0,1],_iv=function(_iw,_ix){var _iy=E(_iw);if(!_iy[0]){var _iz=_iy[1],_iA=E(_ix);if(!_iA[0]){var _iB=_iA[1];return (_iz!=_iB)?(_iz>_iB)?2:0:1;}else{var _iC=I_compareInt(_iA[1],_iz);return (_iC<=0)?(_iC>=0)?1:2:0;}}else{var _iD=_iy[1],_iE=E(_ix);if(!_iE[0]){var _iF=I_compareInt(_iD,_iE[1]);return (_iF>=0)?(_iF<=0)?1:2:0;}else{var _iG=I_compare(_iD,_iE[1]);return (_iG>=0)?(_iG<=0)?1:2:0;}}},_iH=new T(function(){return B(unCStr("GHC.Exception"));}),_iI=new T(function(){return B(unCStr("base"));}),_iJ=new T(function(){return B(unCStr("ArithException"));}),_iK=new T(function(){var _iL=hs_wordToWord64(4194982440),_iM=hs_wordToWord64(3110813675);return [0,_iL,_iM,[0,_iL,_iM,_iI,_iH,_iJ],_3n,_3n];}),_iN=function(_iO){return E(_iK);},_iP=function(_iQ){var _iR=E(_iQ);return new F(function(){return _59(B(_57(_iR[1])),_iN,_iR[2]);});},_iS=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_iT=new T(function(){return B(unCStr("denormal"));}),_iU=new T(function(){return B(unCStr("divide by zero"));}),_iV=new T(function(){return B(unCStr("loss of precision"));}),_iW=new T(function(){return B(unCStr("arithmetic underflow"));}),_iX=new T(function(){return B(unCStr("arithmetic overflow"));}),_iY=function(_iZ,_j0){switch(E(_iZ)){case 0:return new F(function(){return _16(_iX,_j0);});break;case 1:return new F(function(){return _16(_iW,_j0);});break;case 2:return new F(function(){return _16(_iV,_j0);});break;case 3:return new F(function(){return _16(_iU,_j0);});break;case 4:return new F(function(){return _16(_iT,_j0);});break;default:return new F(function(){return _16(_iS,_j0);});}},_j1=function(_j2){return new F(function(){return _iY(_j2,_3n);});},_j3=function(_j4,_j5,_j6){return new F(function(){return _iY(_j5,_j6);});},_j7=function(_j8,_j9){return new F(function(){return _6k(_iY,_j8,_j9);});},_ja=[0,_j3,_j1,_j7],_jb=new T(function(){return [0,_iN,_ja,_jc,_iP,_j1];}),_jc=function(_jd){return [0,_jb,_jd];},_je=3,_jf=new T(function(){return B(_jc(_je));}),_jg=new T(function(){return die(_jf);}),_jh=function(_ji,_jj){var _jk=E(_ji);return (_jk[0]==0)?_jk[1]*Math.pow(2,_jj):I_toNumber(_jk[1])*Math.pow(2,_jj);},_jl=function(_jm,_jn){var _jo=E(_jm);if(!_jo[0]){var _jp=_jo[1],_jq=E(_jn);return (_jq[0]==0)?_jp==_jq[1]:(I_compareInt(_jq[1],_jp)==0)?true:false;}else{var _jr=_jo[1],_js=E(_jn);return (_js[0]==0)?(I_compareInt(_jr,_js[1])==0)?true:false:(I_compare(_jr,_js[1])==0)?true:false;}},_jt=function(_ju){var _jv=E(_ju);if(!_jv[0]){return E(_jv[1]);}else{return new F(function(){return I_toInt(_jv[1]);});}},_jw=function(_jx,_jy){while(1){var _jz=E(_jx);if(!_jz[0]){var _jA=_jz[1],_jB=E(_jy);if(!_jB[0]){var _jC=_jB[1],_jD=addC(_jA,_jC);if(!E(_jD[2])){return [0,_jD[1]];}else{_jx=[1,I_fromInt(_jA)];_jy=[1,I_fromInt(_jC)];continue;}}else{_jx=[1,I_fromInt(_jA)];_jy=_jB;continue;}}else{var _jE=E(_jy);if(!_jE[0]){_jx=_jz;_jy=[1,I_fromInt(_jE[1])];continue;}else{return [1,I_add(_jz[1],_jE[1])];}}}},_jF=function(_jG,_jH){while(1){var _jI=E(_jG);if(!_jI[0]){var _jJ=E(_jI[1]);if(_jJ==(-2147483648)){_jG=[1,I_fromInt(-2147483648)];continue;}else{var _jK=E(_jH);if(!_jK[0]){var _jL=_jK[1];return [0,[0,quot(_jJ,_jL)],[0,_jJ%_jL]];}else{_jG=[1,I_fromInt(_jJ)];_jH=_jK;continue;}}}else{var _jM=E(_jH);if(!_jM[0]){_jG=_jI;_jH=[1,I_fromInt(_jM[1])];continue;}else{var _jN=I_quotRem(_jI[1],_jM[1]);return [0,[1,_jN[1]],[1,_jN[2]]];}}}},_jO=[0,0],_jP=function(_jQ,_jR,_jS){if(!B(_jl(_jS,_jO))){var _jT=B(_jF(_jR,_jS)),_jU=_jT[1];switch(B(_iv(B(_cO(_jT[2],1)),_jS))){case 0:return new F(function(){return _jh(_jU,_jQ);});break;case 1:if(!(B(_jt(_jU))&1)){return new F(function(){return _jh(_jU,_jQ);});}else{return new F(function(){return _jh(B(_jw(_jU,_iu)),_jQ);});}break;default:return new F(function(){return _jh(B(_jw(_jU,_iu)),_jQ);});}}else{return E(_jg);}},_jV=function(_jW,_jX){var _jY=E(_jW);if(!_jY[0]){var _jZ=_jY[1],_k0=E(_jX);return (_k0[0]==0)?_jZ>_k0[1]:I_compareInt(_k0[1],_jZ)<0;}else{var _k1=_jY[1],_k2=E(_jX);return (_k2[0]==0)?I_compareInt(_k1,_k2[1])>0:I_compare(_k1,_k2[1])>0;}},_k3=[0,1],_k4=new T(function(){return B(unCStr("Control.Exception.Base"));}),_k5=new T(function(){return B(unCStr("base"));}),_k6=new T(function(){return B(unCStr("PatternMatchFail"));}),_k7=new T(function(){var _k8=hs_wordToWord64(18445595),_k9=hs_wordToWord64(52003073);return [0,_k8,_k9,[0,_k8,_k9,_k5,_k4,_k6],_3n,_3n];}),_ka=function(_kb){return E(_k7);},_kc=function(_kd){var _ke=E(_kd);return new F(function(){return _59(B(_57(_ke[1])),_ka,_ke[2]);});},_kf=function(_kg){return E(E(_kg)[1]);},_kh=function(_ki){return [0,_kj,_ki];},_kk=function(_kl,_km){return new F(function(){return _16(E(_kl)[1],_km);});},_kn=function(_ko,_kp){return new F(function(){return _6k(_kk,_ko,_kp);});},_kq=function(_kr,_ks,_kt){return new F(function(){return _16(E(_ks)[1],_kt);});},_ku=[0,_kq,_kf,_kn],_kj=new T(function(){return [0,_ka,_ku,_kh,_kc,_kf];}),_kv=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_kw=function(_kx){return E(E(_kx)[3]);},_ky=function(_kz,_kA){return new F(function(){return die(new T(function(){return B(A(_kw,[_kA,_kz]));}));});},_kB=function(_kC,_jd){return new F(function(){return _ky(_kC,_jd);});},_kD=function(_kE,_kF){var _kG=E(_kF);if(!_kG[0]){return [0,_3n,_3n];}else{var _kH=_kG[1];if(!B(A(_kE,[_kH]))){return [0,_3n,_kG];}else{var _kI=new T(function(){var _kJ=B(_kD(_kE,_kG[2]));return [0,_kJ[1],_kJ[2]];});return [0,[1,_kH,new T(function(){return E(E(_kI)[1]);})],new T(function(){return E(E(_kI)[2]);})];}}},_kK=32,_kL=new T(function(){return B(unCStr("\n"));}),_kM=function(_kN){return (E(_kN)==124)?false:true;},_kO=function(_kP,_kQ){var _kR=B(_kD(_kM,B(unCStr(_kP)))),_kS=_kR[1],_kT=function(_kU,_kV){var _kW=new T(function(){var _kX=new T(function(){return B(_16(_kQ,new T(function(){return B(_16(_kV,_kL));},1)));});return B(unAppCStr(": ",_kX));},1);return new F(function(){return _16(_kU,_kW);});},_kY=E(_kR[2]);if(!_kY[0]){return new F(function(){return _kT(_kS,_3n);});}else{if(E(_kY[1])==124){return new F(function(){return _kT(_kS,[1,_kK,_kY[2]]);});}else{return new F(function(){return _kT(_kS,_3n);});}}},_kZ=function(_l0){return new F(function(){return _kB([0,new T(function(){return B(_kO(_l0,_kv));})],_kj);});},_l1=function(_l2){var _l3=_k3,_l4=0;while(1){if(!B(_g9(_l3,_l2))){if(!B(_jV(_l3,_l2))){if(!B(_jl(_l3,_l2))){return new F(function(){return _kZ("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_l4);}}else{return _l4-1|0;}}else{var _l5=B(_cO(_l3,1)),_l6=_l4+1|0;_l3=_l5;_l4=_l6;continue;}}},_l7=function(_l8){var _l9=E(_l8);if(!_l9[0]){var _la=_l9[1]>>>0;if(!_la){return -1;}else{var _lb=1,_lc=0;while(1){if(_lb>=_la){if(_lb<=_la){if(_lb!=_la){return new F(function(){return _kZ("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_lc);}}else{return _lc-1|0;}}else{var _ld=imul(_lb,2)>>>0,_le=_lc+1|0;_lb=_ld;_lc=_le;continue;}}}}else{return new F(function(){return _l1(_l9);});}},_lf=function(_lg){var _lh=E(_lg);if(!_lh[0]){var _li=_lh[1]>>>0;if(!_li){return [0,-1,0];}else{var _lj=function(_lk,_ll){while(1){if(_lk>=_li){if(_lk<=_li){if(_lk!=_li){return new F(function(){return _kZ("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_ll);}}else{return _ll-1|0;}}else{var _lm=imul(_lk,2)>>>0,_ln=_ll+1|0;_lk=_lm;_ll=_ln;continue;}}};return [0,B(_lj(1,0)),(_li&_li-1>>>0)>>>0&4294967295];}}else{var _lo=B(_l7(_lh)),_lp=_lo>>>0;if(!_lp){var _lq=E(_lo);return (_lq==(-2))?[0,-2,0]:[0,_lq,1];}else{var _lr=function(_ls,_lt){while(1){if(_ls>=_lp){if(_ls<=_lp){if(_ls!=_lp){return new F(function(){return _kZ("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_lt);}}else{return _lt-1|0;}}else{var _lu=imul(_ls,2)>>>0,_lv=_lt+1|0;_ls=_lu;_lt=_lv;continue;}}},_lw=B(_lr(1,0));return ((_lw+_lw|0)!=_lo)?[0,_lo,1]:[0,_lo,0];}}},_lx=function(_ly,_lz){var _lA=E(_ly);if(!_lA[0]){var _lB=_lA[1],_lC=E(_lz);return (_lC[0]==0)?_lB<=_lC[1]:I_compareInt(_lC[1],_lB)>=0;}else{var _lD=_lA[1],_lE=E(_lz);return (_lE[0]==0)?I_compareInt(_lD,_lE[1])<=0:I_compare(_lD,_lE[1])<=0;}},_lF=function(_lG,_lH){while(1){var _lI=E(_lG);if(!_lI[0]){var _lJ=_lI[1],_lK=E(_lH);if(!_lK[0]){return [0,(_lJ>>>0&_lK[1]>>>0)>>>0&4294967295];}else{_lG=[1,I_fromInt(_lJ)];_lH=_lK;continue;}}else{var _lL=E(_lH);if(!_lL[0]){_lG=_lI;_lH=[1,I_fromInt(_lL[1])];continue;}else{return [1,I_and(_lI[1],_lL[1])];}}}},_lM=function(_lN,_lO){while(1){var _lP=E(_lN);if(!_lP[0]){var _lQ=_lP[1],_lR=E(_lO);if(!_lR[0]){var _lS=_lR[1],_lT=subC(_lQ,_lS);if(!E(_lT[2])){return [0,_lT[1]];}else{_lN=[1,I_fromInt(_lQ)];_lO=[1,I_fromInt(_lS)];continue;}}else{_lN=[1,I_fromInt(_lQ)];_lO=_lR;continue;}}else{var _lU=E(_lO);if(!_lU[0]){_lN=_lP;_lO=[1,I_fromInt(_lU[1])];continue;}else{return [1,I_sub(_lP[1],_lU[1])];}}}},_lV=[0,2],_lW=function(_lX,_lY){var _lZ=E(_lX);if(!_lZ[0]){var _m0=(_lZ[1]>>>0&(2<<_lY>>>0)-1>>>0)>>>0,_m1=1<<_lY>>>0;return (_m1<=_m0)?(_m1>=_m0)?1:2:0;}else{var _m2=B(_lF(_lZ,B(_lM(B(_cO(_lV,_lY)),_k3)))),_m3=B(_cO(_k3,_lY));return (!B(_jV(_m3,_m2)))?(!B(_g9(_m3,_m2)))?1:2:0;}},_m4=function(_m5,_m6){while(1){var _m7=E(_m5);if(!_m7[0]){_m5=[1,I_fromInt(_m7[1])];continue;}else{return [1,I_shiftRight(_m7[1],_m6)];}}},_m8=function(_m9,_ma,_mb,_mc){var _md=B(_lf(_mc)),_me=_md[1];if(!E(_md[2])){var _mf=B(_l7(_mb));if(_mf<((_me+_m9|0)-1|0)){var _mg=_me+(_m9-_ma|0)|0;if(_mg>0){if(_mg>_mf){if(_mg<=(_mf+1|0)){if(!E(B(_lf(_mb))[2])){return 0;}else{return new F(function(){return _jh(_iu,_m9-_ma|0);});}}else{return 0;}}else{var _mh=B(_m4(_mb,_mg));switch(B(_lW(_mb,_mg-1|0))){case 0:return new F(function(){return _jh(_mh,_m9-_ma|0);});break;case 1:if(!(B(_jt(_mh))&1)){return new F(function(){return _jh(_mh,_m9-_ma|0);});}else{return new F(function(){return _jh(B(_jw(_mh,_iu)),_m9-_ma|0);});}break;default:return new F(function(){return _jh(B(_jw(_mh,_iu)),_m9-_ma|0);});}}}else{return new F(function(){return _jh(_mb,(_m9-_ma|0)-_mg|0);});}}else{if(_mf>=_ma){var _mi=B(_m4(_mb,(_mf+1|0)-_ma|0));switch(B(_lW(_mb,_mf-_ma|0))){case 0:return new F(function(){return _jh(_mi,((_mf-_me|0)+1|0)-_ma|0);});break;case 2:return new F(function(){return _jh(B(_jw(_mi,_iu)),((_mf-_me|0)+1|0)-_ma|0);});break;default:if(!(B(_jt(_mi))&1)){return new F(function(){return _jh(_mi,((_mf-_me|0)+1|0)-_ma|0);});}else{return new F(function(){return _jh(B(_jw(_mi,_iu)),((_mf-_me|0)+1|0)-_ma|0);});}}}else{return new F(function(){return _jh(_mb, -_me);});}}}else{var _mj=B(_l7(_mb))-_me|0,_mk=function(_ml){var _mm=function(_mn,_mo){if(!B(_lx(B(_cO(_mo,_ma)),_mn))){return new F(function(){return _jP(_ml-_ma|0,_mn,_mo);});}else{return new F(function(){return _jP((_ml-_ma|0)+1|0,_mn,B(_cO(_mo,1)));});}};if(_ml>=_ma){if(_ml!=_ma){return new F(function(){return _mm(_mb,new T(function(){return B(_cO(_mc,_ml-_ma|0));}));});}else{return new F(function(){return _mm(_mb,_mc);});}}else{return new F(function(){return _mm(new T(function(){return B(_cO(_mb,_ma-_ml|0));}),_mc);});}};if(_m9>_mj){return new F(function(){return _mk(_m9);});}else{return new F(function(){return _mk(_mj);});}}},_mp=[0,2147483647],_mq=new T(function(){return B(_jw(_mp,_k3));}),_mr=function(_ms){var _mt=E(_ms);if(!_mt[0]){var _mu=E(_mt[1]);return (_mu==(-2147483648))?E(_mq):[0, -_mu];}else{return [1,I_negate(_mt[1])];}},_mv=new T(function(){return 0/0;}),_mw=new T(function(){return -1/0;}),_mx=new T(function(){return 1/0;}),_my=0,_mz=function(_mA,_mB){if(!B(_jl(_mB,_jO))){if(!B(_jl(_mA,_jO))){if(!B(_g9(_mA,_jO))){return new F(function(){return _m8(-1021,53,_mA,_mB);});}else{return  -B(_m8(-1021,53,B(_mr(_mA)),_mB));}}else{return E(_my);}}else{return (!B(_jl(_mA,_jO)))?(!B(_g9(_mA,_jO)))?E(_mx):E(_mw):E(_mv);}},_mC=function(_mD){var _mE=E(_mD);return new F(function(){return _mz(_mE[1],_mE[2]);});},_mF=function(_mG){return 1/E(_mG);},_mH=function(_mI){var _mJ=E(_mI),_mK=E(_mJ);return (_mK==0)?E(_my):(_mK<=0)? -_mK:E(_mJ);},_mL=function(_mM){return new F(function(){return _bL(_mM);});},_mN=1,_mO=-1,_mP=function(_mQ){var _mR=E(_mQ);return (_mR<=0)?(_mR>=0)?E(_mR):E(_mO):E(_mN);},_mS=function(_mT,_mU){return E(_mT)-E(_mU);},_mV=function(_mW){return  -E(_mW);},_mX=function(_mY,_mZ){return E(_mY)+E(_mZ);},_n0=function(_n1,_n2){return E(_n1)*E(_n2);},_n3=[0,_mX,_mS,_n0,_mV,_mH,_mP,_mL],_n4=function(_n5,_n6){return E(_n5)/E(_n6);},_n7=[0,_n3,_n4,_mF,_mC],_n8=function(_n9){return new F(function(){return Math.acos(E(_n9));});},_na=function(_nb){return new F(function(){return Math.asin(E(_nb));});},_nc=function(_nd){return new F(function(){return Math.atan(E(_nd));});},_ne=function(_nf){return new F(function(){return Math.cos(E(_nf));});},_ng=function(_nh){return new F(function(){return cosh(E(_nh));});},_ni=function(_nj){return new F(function(){return Math.exp(E(_nj));});},_nk=function(_nl){return new F(function(){return Math.log(E(_nl));});},_nm=function(_nn,_no){return new F(function(){return Math.pow(E(_nn),E(_no));});},_np=function(_nq){return new F(function(){return Math.sin(E(_nq));});},_nr=function(_ns){return new F(function(){return sinh(E(_ns));});},_nt=function(_nu){return new F(function(){return Math.sqrt(E(_nu));});},_nv=function(_nw){return new F(function(){return Math.tan(E(_nw));});},_nx=function(_ny){return new F(function(){return tanh(E(_ny));});},_nz=[0,_n7,_it,_ni,_nk,_nt,_nm,_iq,_np,_ne,_nv,_na,_n8,_nc,_nr,_ng,_nx,_ik,_ih,_in],_nA=function(_nB,_nC){if(_nC<=0){var _nD=function(_nE){var _nF=function(_nG){var _nH=function(_nI){var _nJ=function(_nK){var _nL=isDoubleNegativeZero(_nC),_nM=_nL,_nN=function(_nO){var _nP=E(_nB);if(!_nP){return (_nC>=0)?(E(_nM)==0)?E(_nC):3.141592653589793:3.141592653589793;}else{var _nQ=E(_nC);return (_nQ==0)?E(_nP):_nQ+_nP;}};if(!E(_nM)){return new F(function(){return _nN(_);});}else{var _nR=E(_nB),_nS=isDoubleNegativeZero(_nR);if(!E(_nS)){return new F(function(){return _nN(_);});}else{return  -B(_nA( -_nR,_nC));}}};if(_nC>=0){return new F(function(){return _nJ(_);});}else{var _nT=E(_nB),_nU=isDoubleNegativeZero(_nT);if(!E(_nU)){return new F(function(){return _nJ(_);});}else{return  -B(_nA( -_nT,_nC));}}};if(_nC>0){return new F(function(){return _nH(_);});}else{var _nV=E(_nB);if(_nV>=0){return new F(function(){return _nH(_);});}else{return  -B(_nA( -_nV,_nC));}}};if(_nC>=0){return new F(function(){return _nF(_);});}else{var _nW=E(_nB);if(_nW<=0){return new F(function(){return _nF(_);});}else{return 3.141592653589793+Math.atan(_nW/_nC);}}};if(!E(_nC)){if(E(_nB)<=0){return new F(function(){return _nD(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _nD(_);});}}else{return new F(function(){return Math.atan(E(_nB)/_nC);});}},_nX=function(_nY,_nZ){return new F(function(){return _nA(_nY,E(_nZ));});},_o0=function(_o1){var _o2=B(_bI(E(_o1)));return [0,_o2[1],_o2[2]];},_o3=function(_o4,_o5){return new F(function(){return _jh(_o4,E(_o5));});},_o6=function(_o7){var _o8=B(_bI(_o7));return (!B(_jl(_o8[1],_jO)))?_o8[2]+53|0:0;},_o9=function(_oa){return new F(function(){return _o6(E(_oa));});},_ob=53,_oc=function(_od){return E(_ob);},_oe=[0,2],_of=function(_og){return E(_oe);},_oh=1024,_oi=-1021,_oj=[0,_oi,_oh],_ok=function(_ol){return E(_oj);},_om=function(_on){var _oo=isDoubleDenormalized(E(_on));return (E(_oo)==0)?false:true;},_op=function(_oq){return true;},_or=function(_os){var _ot=isDoubleInfinite(E(_os));return (E(_ot)==0)?false:true;},_ou=function(_ov){var _ow=isDoubleNaN(E(_ov));return (E(_ow)==0)?false:true;},_ox=function(_oy){var _oz=isDoubleNegativeZero(E(_oy));return (E(_oz)==0)?false:true;},_oA=function(_oB,_oC){var _oD=E(_oB);if(!_oD){return E(_oC);}else{var _oE=E(_oC);if(!_oE){return 0;}else{var _oF=isDoubleFinite(_oE);if(!E(_oF)){return E(_oE);}else{var _oG=B(_bI(_oE)),_oH=_oG[1],_oI=_oG[2];if(2257>_oD){if(-2257>_oD){return new F(function(){return _jh(_oH,_oI+(-2257)|0);});}else{return new F(function(){return _jh(_oH,_oI+_oD|0);});}}else{return new F(function(){return _jh(_oH,_oI+2257|0);});}}}}},_oJ=function(_oK,_oL){return new F(function(){return _oA(E(_oK),E(_oL));});},_oM=function(_oN){return new F(function(){return _jh(B(_bI(E(_oN)))[1],-53);});},_oO=function(_oP,_oQ){return (E(_oP)!=E(_oQ))?true:false;},_oR=function(_oS,_oT){return E(_oS)==E(_oT);},_oU=[0,_oR,_oO],_oV=function(_oW,_oX){return E(_oW)<E(_oX);},_oY=function(_oZ,_p0){return E(_oZ)<=E(_p0);},_p1=function(_p2,_p3){return E(_p2)>E(_p3);},_p4=function(_p5,_p6){return E(_p5)>=E(_p6);},_p7=function(_p8,_p9){var _pa=E(_p8),_pb=E(_p9);return (_pa>=_pb)?(_pa!=_pb)?2:1:0;},_pc=function(_pd,_pe){var _pf=E(_pd),_pg=E(_pe);return (_pf>_pg)?E(_pf):E(_pg);},_ph=function(_pi,_pj){var _pk=E(_pi),_pl=E(_pj);return (_pk>_pl)?E(_pl):E(_pk);},_pm=[0,_oU,_p7,_oV,_oY,_p1,_p4,_pc,_ph],_pn=new T(function(){var _po=newByteArr(256),_pp=_po,_=_pp["v"]["i8"][0]=8,_pq=function(_pr,_ps,_pt,_){while(1){if(_pt>=256){if(_pr>=256){return E(_);}else{var _pu=imul(2,_pr)|0,_pv=_ps+1|0,_pw=_pr;_pr=_pu;_ps=_pv;_pt=_pw;continue;}}else{var _=_pp["v"]["i8"][_pt]=_ps,_pw=_pt+_pr|0;_pt=_pw;continue;}}},_=B(_pq(2,0,1,_));return _pp;}),_px=function(_py,_pz){while(1){var _pA=B((function(_pB,_pC){var _pD=hs_int64ToInt(_pB),_pE=E(_pn)["v"]["i8"][(255&_pD>>>0)>>>0&4294967295];if(_pC>_pE){if(_pE>=8){var _pF=hs_uncheckedIShiftRA64(_pB,8),_pG=_pC-8|0;_py=_pF;_pz=_pG;return null;}else{return [0,new T(function(){var _pH=hs_uncheckedIShiftRA64(_pB,_pE);return B(_bQ(_pH));}),_pC-_pE|0];}}else{return [0,new T(function(){var _pI=hs_uncheckedIShiftRA64(_pB,_pC);return B(_bQ(_pI));}),0];}})(_py,_pz));if(_pA!=null){return _pA;}}},_pJ=function(_pK){return I_toInt(_pK)>>>0;},_pL=function(_pM){var _pN=E(_pM);if(!_pN[0]){return _pN[1]>>>0;}else{return new F(function(){return _pJ(_pN[1]);});}},_pO=function(_pP){var _pQ=B(_bI(_pP)),_pR=_pQ[1],_pS=_pQ[2];if(_pS<0){var _pT=function(_pU){if(!_pU){return [0,E(_pR),B(_cO(_iu, -_pS))];}else{var _pV=B(_px(B(_c0(_pR)), -_pS));return [0,E(_pV[1]),B(_cO(_iu,_pV[2]))];}};if(!((B(_pL(_pR))&1)>>>0)){return new F(function(){return _pT(1);});}else{return new F(function(){return _pT(0);});}}else{return [0,B(_cO(_pR,_pS)),_iu];}},_pW=function(_pX){var _pY=B(_pO(E(_pX)));return [0,E(_pY[1]),E(_pY[2])];},_pZ=[0,_n3,_pm,_pW],_q0=function(_q1){return E(E(_q1)[1]);},_q2=function(_q3){return E(E(_q3)[1]);},_q4=[0,1],_q5=function(_q6,_q7){if(_q6<=_q7){var _q8=function(_q9){return [1,_q9,new T(function(){if(_q9!=_q7){return B(_q8(_q9+1|0));}else{return [0];}})];};return new F(function(){return _q8(_q6);});}else{return [0];}},_qa=function(_qb){return new F(function(){return _q5(E(_qb),2147483647);});},_qc=function(_qd,_qe,_qf){if(_qf<=_qe){var _qg=new T(function(){var _qh=_qe-_qd|0,_qi=function(_qj){return (_qj>=(_qf-_qh|0))?[1,_qj,new T(function(){return B(_qi(_qj+_qh|0));})]:[1,_qj,_3n];};return B(_qi(_qe));});return [1,_qd,_qg];}else{return (_qf<=_qd)?[1,_qd,_3n]:[0];}},_qk=function(_ql,_qm,_qn){if(_qn>=_qm){var _qo=new T(function(){var _qp=_qm-_ql|0,_qq=function(_qr){return (_qr<=(_qn-_qp|0))?[1,_qr,new T(function(){return B(_qq(_qr+_qp|0));})]:[1,_qr,_3n];};return B(_qq(_qm));});return [1,_ql,_qo];}else{return (_qn>=_ql)?[1,_ql,_3n]:[0];}},_qs=function(_qt,_qu){if(_qu<_qt){return new F(function(){return _qc(_qt,_qu,-2147483648);});}else{return new F(function(){return _qk(_qt,_qu,2147483647);});}},_qv=function(_qw,_qx){return new F(function(){return _qs(E(_qw),E(_qx));});},_qy=function(_qz,_qA,_qB){if(_qA<_qz){return new F(function(){return _qc(_qz,_qA,_qB);});}else{return new F(function(){return _qk(_qz,_qA,_qB);});}},_qC=function(_qD,_qE,_qF){return new F(function(){return _qy(E(_qD),E(_qE),E(_qF));});},_qG=function(_qH,_qI){return new F(function(){return _q5(E(_qH),E(_qI));});},_qJ=function(_qK){return E(_qK);},_qL=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_qM=new T(function(){return B(err(_qL));}),_qN=function(_qO){var _qP=E(_qO);return (_qP==(-2147483648))?E(_qM):_qP-1|0;},_qQ=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_qR=new T(function(){return B(err(_qQ));}),_qS=function(_qT){var _qU=E(_qT);return (_qU==2147483647)?E(_qR):_qU+1|0;},_qV=[0,_qS,_qN,_qJ,_qJ,_qa,_qv,_qG,_qC],_qW=function(_qX,_qY){if(_qX<=0){if(_qX>=0){return new F(function(){return quot(_qX,_qY);});}else{if(_qY<=0){return new F(function(){return quot(_qX,_qY);});}else{return quot(_qX+1|0,_qY)-1|0;}}}else{if(_qY>=0){if(_qX>=0){return new F(function(){return quot(_qX,_qY);});}else{if(_qY<=0){return new F(function(){return quot(_qX,_qY);});}else{return quot(_qX+1|0,_qY)-1|0;}}}else{return quot(_qX-1|0,_qY)-1|0;}}},_qZ=0,_r0=new T(function(){return B(_jc(_qZ));}),_r1=new T(function(){return die(_r0);}),_r2=function(_r3,_r4){var _r5=E(_r4);switch(_r5){case -1:var _r6=E(_r3);if(_r6==(-2147483648)){return E(_r1);}else{return new F(function(){return _qW(_r6,-1);});}break;case 0:return E(_jg);default:return new F(function(){return _qW(_r3,_r5);});}},_r7=function(_r8,_r9){return new F(function(){return _r2(E(_r8),E(_r9));});},_ra=0,_rb=[0,_r1,_ra],_rc=function(_rd,_re){var _rf=E(_rd),_rg=E(_re);switch(_rg){case -1:var _rh=E(_rf);if(_rh==(-2147483648)){return E(_rb);}else{if(_rh<=0){if(_rh>=0){var _ri=quotRemI(_rh,-1);return [0,_ri[1],_ri[2]];}else{var _rj=quotRemI(_rh,-1);return [0,_rj[1],_rj[2]];}}else{var _rk=quotRemI(_rh-1|0,-1);return [0,_rk[1]-1|0,(_rk[2]+(-1)|0)+1|0];}}break;case 0:return E(_jg);default:if(_rf<=0){if(_rf>=0){var _rl=quotRemI(_rf,_rg);return [0,_rl[1],_rl[2]];}else{if(_rg<=0){var _rm=quotRemI(_rf,_rg);return [0,_rm[1],_rm[2]];}else{var _rn=quotRemI(_rf+1|0,_rg);return [0,_rn[1]-1|0,(_rn[2]+_rg|0)-1|0];}}}else{if(_rg>=0){if(_rf>=0){var _ro=quotRemI(_rf,_rg);return [0,_ro[1],_ro[2]];}else{if(_rg<=0){var _rp=quotRemI(_rf,_rg);return [0,_rp[1],_rp[2]];}else{var _rq=quotRemI(_rf+1|0,_rg);return [0,_rq[1]-1|0,(_rq[2]+_rg|0)-1|0];}}}else{var _rr=quotRemI(_rf-1|0,_rg);return [0,_rr[1]-1|0,(_rr[2]+_rg|0)+1|0];}}}},_rs=function(_rt,_ru){var _rv=_rt%_ru;if(_rt<=0){if(_rt>=0){return E(_rv);}else{if(_ru<=0){return E(_rv);}else{var _rw=E(_rv);return (_rw==0)?0:_rw+_ru|0;}}}else{if(_ru>=0){if(_rt>=0){return E(_rv);}else{if(_ru<=0){return E(_rv);}else{var _rx=E(_rv);return (_rx==0)?0:_rx+_ru|0;}}}else{var _ry=E(_rv);return (_ry==0)?0:_ry+_ru|0;}}},_rz=function(_rA,_rB){var _rC=E(_rB);switch(_rC){case -1:return E(_ra);case 0:return E(_jg);default:return new F(function(){return _rs(E(_rA),_rC);});}},_rD=function(_rE,_rF){var _rG=E(_rE),_rH=E(_rF);switch(_rH){case -1:var _rI=E(_rG);if(_rI==(-2147483648)){return E(_r1);}else{return new F(function(){return quot(_rI,-1);});}break;case 0:return E(_jg);default:return new F(function(){return quot(_rG,_rH);});}},_rJ=function(_rK,_rL){var _rM=E(_rK),_rN=E(_rL);switch(_rN){case -1:var _rO=E(_rM);if(_rO==(-2147483648)){return E(_rb);}else{var _rP=quotRemI(_rO,-1);return [0,_rP[1],_rP[2]];}break;case 0:return E(_jg);default:var _rQ=quotRemI(_rM,_rN);return [0,_rQ[1],_rQ[2]];}},_rR=function(_rS,_rT){var _rU=E(_rT);switch(_rU){case -1:return E(_ra);case 0:return E(_jg);default:return E(_rS)%_rU;}},_rV=function(_rW){return new F(function(){return _bO(E(_rW));});},_rX=function(_rY){return [0,E(B(_bO(E(_rY)))),E(_q4)];},_rZ=function(_s0,_s1){return imul(E(_s0),E(_s1))|0;},_s2=function(_s3,_s4){return E(_s3)+E(_s4)|0;},_s5=function(_s6,_s7){return E(_s6)-E(_s7)|0;},_s8=function(_s9){var _sa=E(_s9);return (_sa<0)? -_sa:E(_sa);},_sb=function(_sc){return new F(function(){return _jt(_sc);});},_sd=function(_se){return  -E(_se);},_sf=-1,_sg=0,_sh=1,_si=function(_sj){var _sk=E(_sj);return (_sk>=0)?(E(_sk)==0)?E(_sg):E(_sh):E(_sf);},_sl=[0,_s2,_s5,_rZ,_sd,_s8,_si,_sb],_sm=function(_sn,_so){return E(_sn)==E(_so);},_sp=function(_sq,_sr){return E(_sq)!=E(_sr);},_ss=[0,_sm,_sp],_st=function(_su,_sv){var _sw=E(_su),_sx=E(_sv);return (_sw>_sx)?E(_sw):E(_sx);},_sy=function(_sz,_sA){var _sB=E(_sz),_sC=E(_sA);return (_sB>_sC)?E(_sC):E(_sB);},_sD=function(_sE,_sF){return (_sE>=_sF)?(_sE!=_sF)?2:1:0;},_sG=function(_sH,_sI){return new F(function(){return _sD(E(_sH),E(_sI));});},_sJ=function(_sK,_sL){return E(_sK)>=E(_sL);},_sM=function(_sN,_sO){return E(_sN)>E(_sO);},_sP=function(_sQ,_sR){return E(_sQ)<=E(_sR);},_sS=function(_sT,_sU){return E(_sT)<E(_sU);},_sV=[0,_ss,_sG,_sS,_sP,_sM,_sJ,_st,_sy],_sW=[0,_sl,_sV,_rX],_sX=[0,_sW,_qV,_rD,_rR,_r7,_rz,_rJ,_rc,_rV],_sY=function(_sZ,_t0){while(1){var _t1=E(_sZ);if(!_t1[0]){var _t2=_t1[1],_t3=E(_t0);if(!_t3[0]){var _t4=_t3[1];if(!(imul(_t2,_t4)|0)){return [0,imul(_t2,_t4)|0];}else{_sZ=[1,I_fromInt(_t2)];_t0=[1,I_fromInt(_t4)];continue;}}else{_sZ=[1,I_fromInt(_t2)];_t0=_t3;continue;}}else{var _t5=E(_t0);if(!_t5[0]){_sZ=_t1;_t0=[1,I_fromInt(_t5[1])];continue;}else{return [1,I_mul(_t1[1],_t5[1])];}}}},_t6=function(_t7,_t8,_t9){while(1){if(!(_t8%2)){var _ta=B(_sY(_t7,_t7)),_tb=quot(_t8,2);_t7=_ta;_t8=_tb;continue;}else{var _tc=E(_t8);if(_tc==1){return new F(function(){return _sY(_t7,_t9);});}else{var _ta=B(_sY(_t7,_t7)),_td=B(_sY(_t7,_t9));_t7=_ta;_t8=quot(_tc-1|0,2);_t9=_td;continue;}}}},_te=function(_tf,_tg){while(1){if(!(_tg%2)){var _th=B(_sY(_tf,_tf)),_ti=quot(_tg,2);_tf=_th;_tg=_ti;continue;}else{var _tj=E(_tg);if(_tj==1){return E(_tf);}else{return new F(function(){return _t6(B(_sY(_tf,_tf)),quot(_tj-1|0,2),_tf);});}}}},_tk=function(_tl){return E(E(_tl)[3]);},_tm=function(_tn){return E(E(_tn)[1]);},_to=function(_tp){return E(E(_tp)[2]);},_tq=function(_tr){return E(E(_tr)[2]);},_ts=function(_tt){return E(E(_tt)[3]);},_tu=[0,0],_tv=[0,2],_tw=function(_tx){return E(E(_tx)[7]);},_ty=function(_tz){return E(E(_tz)[4]);},_tA=function(_tB,_tC){var _tD=B(_q0(_tB)),_tE=new T(function(){return B(_q2(_tD));}),_tF=new T(function(){return B(A(_ty,[_tB,_tC,new T(function(){return B(A(_tw,[_tE,_tv]));})]));});return new F(function(){return A(_T,[B(_tm(B(_to(_tD)))),_tF,new T(function(){return B(A(_tw,[_tE,_tu]));})]);});},_tG=new T(function(){return B(unCStr("Negative exponent"));}),_tH=new T(function(){return B(err(_tG));}),_tI=function(_tJ){return E(E(_tJ)[3]);},_tK=function(_tL,_tM,_tN,_tO){var _tP=B(_q0(_tM)),_tQ=new T(function(){return B(_q2(_tP));}),_tR=B(_to(_tP));if(!B(A(_ts,[_tR,_tO,new T(function(){return B(A(_tw,[_tQ,_tu]));})]))){if(!B(A(_T,[B(_tm(_tR)),_tO,new T(function(){return B(A(_tw,[_tQ,_tu]));})]))){var _tS=new T(function(){return B(A(_tw,[_tQ,_tv]));}),_tT=new T(function(){return B(A(_tw,[_tQ,_q4]));}),_tU=B(_tm(_tR)),_tV=function(_tW,_tX,_tY){while(1){var _tZ=B((function(_u0,_u1,_u2){if(!B(_tA(_tM,_u1))){if(!B(A(_T,[_tU,_u1,_tT]))){var _u3=new T(function(){return B(A(_tI,[_tM,new T(function(){return B(A(_tq,[_tQ,_u1,_tT]));}),_tS]));});_tW=new T(function(){return B(A(_tk,[_tL,_u0,_u0]));});_tX=_u3;_tY=new T(function(){return B(A(_tk,[_tL,_u0,_u2]));});return null;}else{return new F(function(){return A(_tk,[_tL,_u0,_u2]);});}}else{var _u4=_u2;_tW=new T(function(){return B(A(_tk,[_tL,_u0,_u0]));});_tX=new T(function(){return B(A(_tI,[_tM,_u1,_tS]));});_tY=_u4;return null;}})(_tW,_tX,_tY));if(_tZ!=null){return _tZ;}}},_u5=_tN,_u6=_tO;while(1){var _u7=B((function(_u8,_u9){if(!B(_tA(_tM,_u9))){if(!B(A(_T,[_tU,_u9,_tT]))){var _ua=new T(function(){return B(A(_tI,[_tM,new T(function(){return B(A(_tq,[_tQ,_u9,_tT]));}),_tS]));});return new F(function(){return _tV(new T(function(){return B(A(_tk,[_tL,_u8,_u8]));}),_ua,_u8);});}else{return E(_u8);}}else{_u5=new T(function(){return B(A(_tk,[_tL,_u8,_u8]));});_u6=new T(function(){return B(A(_tI,[_tM,_u9,_tS]));});return null;}})(_u5,_u6));if(_u7!=null){return _u7;}}}else{return new F(function(){return A(_tw,[_tL,_q4]);});}}else{return E(_tH);}},_ub=new T(function(){return B(err(_tG));}),_uc=function(_ud,_ue){var _uf=B(_bI(_ue)),_ug=_uf[1],_uh=_uf[2],_ui=new T(function(){return B(_q2(new T(function(){return B(_q0(_ud));})));});if(_uh<0){var _uj= -_uh;if(_uj>=0){var _uk=E(_uj);if(!_uk){var _ul=E(_q4);}else{var _ul=B(_te(_oe,_uk));}if(!B(_jl(_ul,_jO))){var _um=B(_jF(_ug,_ul));return [0,new T(function(){return B(A(_tw,[_ui,_um[1]]));}),new T(function(){return B(_jh(_um[2],_uh));})];}else{return E(_jg);}}else{return E(_ub);}}else{var _un=new T(function(){var _uo=new T(function(){return B(_tK(_ui,_sX,new T(function(){return B(A(_tw,[_ui,_oe]));}),_uh));});return B(A(_tk,[_ui,new T(function(){return B(A(_tw,[_ui,_ug]));}),_uo]));});return [0,_un,_my];}},_up=function(_uq){return E(E(_uq)[1]);},_ur=function(_us,_ut){var _uu=B(_uc(_us,E(_ut))),_uv=_uu[1];if(E(_uu[2])<=0){return E(_uv);}else{var _uw=B(_q2(B(_q0(_us))));return new F(function(){return A(_up,[_uw,_uv,new T(function(){return B(A(_tw,[_uw,_iu]));})]);});}},_ux=function(_uy,_uz){var _uA=B(_uc(_uy,E(_uz))),_uB=_uA[1];if(E(_uA[2])>=0){return E(_uB);}else{var _uC=B(_q2(B(_q0(_uy))));return new F(function(){return A(_tq,[_uC,_uB,new T(function(){return B(A(_tw,[_uC,_iu]));})]);});}},_uD=function(_uE,_uF){var _uG=B(_uc(_uE,E(_uF)));return [0,_uG[1],_uG[2]];},_uH=function(_uI,_uJ){var _uK=B(_uc(_uI,_uJ)),_uL=_uK[1],_uM=E(_uK[2]),_uN=new T(function(){var _uO=B(_q2(B(_q0(_uI))));if(_uM>=0){return B(A(_up,[_uO,_uL,new T(function(){return B(A(_tw,[_uO,_iu]));})]));}else{return B(A(_tq,[_uO,_uL,new T(function(){return B(A(_tw,[_uO,_iu]));})]));}}),_uP=function(_uQ){var _uR=_uQ-0.5;return (_uR>=0)?(E(_uR)==0)?(!B(_tA(_uI,_uL)))?E(_uN):E(_uL):E(_uN):E(_uL);},_uS=E(_uM);if(!_uS){return new F(function(){return _uP(0);});}else{if(_uS<=0){var _uT= -_uS-0.5;return (_uT>=0)?(E(_uT)==0)?(!B(_tA(_uI,_uL)))?E(_uN):E(_uL):E(_uN):E(_uL);}else{return new F(function(){return _uP(_uS);});}}},_uU=function(_uV,_uW){return new F(function(){return _uH(_uV,E(_uW));});},_uX=function(_uY,_uZ){return E(B(_uc(_uY,E(_uZ)))[1]);},_v0=[0,_pZ,_n7,_uD,_uX,_uU,_ur,_ux],_v1=[0,_v0,_nz,_of,_oc,_ok,_o0,_o3,_o9,_oM,_oJ,_ou,_or,_om,_ox,_op,_nX],_v2=0,_v3=1,_v4=2,_v5=false,_v6=true,_v7=function(_v8){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_83(9,_v8,_3n));}))));});},_v9=1,_va=function(_vb){return new F(function(){return err(B(unAppCStr("Char.intToDigit: not a digit ",new T(function(){if(_vb>=0){var _vc=jsShowI(_vb);return fromJSStr(_vc);}else{var _vd=jsShowI(_vb);return fromJSStr(_vd);}}))));});},_ve=function(_vf){var _vg=function(_vh){if(_vf<10){return new F(function(){return _va(_vf);});}else{if(_vf>15){return new F(function(){return _va(_vf);});}else{return (97+_vf|0)-10|0;}}};if(_vf<0){return new F(function(){return _vg(_);});}else{if(_vf>9){return new F(function(){return _vg(_);});}else{return 48+_vf|0;}}},_vi=function(_vj){return new F(function(){return _ve(E(_vj));});},_vk=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_vl=function(_vm){return new F(function(){return _kB([0,new T(function(){return B(_kO(_vm,_vk));})],_kj);});},_vn=new T(function(){return B(_vl("GHC\\Float.hs:622:11-64|d : ds\'"));}),_vo=0,_vp=function(_vq,_vr){if(E(_vq)<=0){var _vs=B(_1A(_vi,[1,_vo,_vr]));return (_vs[0]==0)?E(_vn):[0,_vs[1],_vs[2]];}else{var _vt=B(_1A(_vi,_vr));return (_vt[0]==0)?E(_vn):[0,_vt[1],_vt[2]];}},_vu=function(_vv){return E(E(_vv)[1]);},_vw=function(_vx){return E(E(_vx)[1]);},_vy=function(_vz){return E(E(_vz)[1]);},_vA=function(_vB){return E(E(_vB)[1]);},_vC=function(_vD){return E(E(_vD)[2]);},_vE=46,_vF=48,_vG=new T(function(){return B(unCStr("0"));}),_vH=function(_vI,_vJ,_vK){while(1){var _vL=B((function(_vM,_vN,_vO){var _vP=E(_vM);if(!_vP){var _vQ=B(_cJ(_vN,_3n));if(!_vQ[0]){return new F(function(){return _16(_vG,[1,_vE,new T(function(){var _vR=E(_vO);if(!_vR[0]){return E(_vG);}else{return E(_vR);}})]);});}else{return new F(function(){return _16(_vQ,[1,_vE,new T(function(){var _vS=E(_vO);if(!_vS[0]){return E(_vG);}else{return E(_vS);}})]);});}}else{var _vT=E(_vO);if(!_vT[0]){var _vU=[1,_vF,_vN];_vI=_vP-1|0;_vJ=_vU;_vK=_3n;return null;}else{var _vU=[1,_vT[1],_vN];_vI=_vP-1|0;_vJ=_vU;_vK=_vT[2];return null;}}})(_vI,_vJ,_vK));if(_vL!=null){return _vL;}}},_vV=function(_vW){return new F(function(){return _83(0,E(_vW),_3n);});},_vX=function(_vY,_vZ,_w0){return new F(function(){return _83(E(_vY),E(_vZ),_w0);});},_w1=function(_w2,_w3){return new F(function(){return _83(0,E(_w2),_w3);});},_w4=function(_w5,_w6){return new F(function(){return _6k(_w1,_w5,_w6);});},_w7=[0,_vX,_vV,_w4],_w8=0,_w9=function(_wa,_wb,_wc){return new F(function(){return A(_wa,[[1,_6h,new T(function(){return B(A(_wb,[_wc]));})]]);});},_wd=new T(function(){return B(unCStr("foldr1"));}),_we=new T(function(){return B(_1q(_wd));}),_wf=function(_wg,_wh){var _wi=E(_wh);if(!_wi[0]){return E(_we);}else{var _wj=_wi[1],_wk=E(_wi[2]);if(!_wk[0]){return E(_wj);}else{return new F(function(){return A(_wg,[_wj,new T(function(){return B(_wf(_wg,_wk));})]);});}}},_wl=new T(function(){return B(unCStr(" out of range "));}),_wm=new T(function(){return B(unCStr("}.index: Index "));}),_wn=new T(function(){return B(unCStr("Ix{"));}),_wo=[1,_81,_3n],_wp=[1,_81,_wo],_wq=0,_wr=function(_ws){return E(E(_ws)[1]);},_wt=function(_wu,_wv,_ww,_wx,_wy){var _wz=new T(function(){var _wA=new T(function(){var _wB=new T(function(){var _wC=new T(function(){var _wD=new T(function(){return B(A(_wf,[_w9,[1,new T(function(){return B(A(_wr,[_ww,_wq,_wx]));}),[1,new T(function(){return B(A(_wr,[_ww,_wq,_wy]));}),_3n]],_wp]));});return B(_16(_wl,[1,_82,[1,_82,_wD]]));});return B(A(_wr,[_ww,_w8,_wv,[1,_81,_wC]]));});return B(_16(_wm,[1,_82,_wB]));},1);return B(_16(_wu,_wA));},1);return new F(function(){return err(B(_16(_wn,_wz)));});},_wE=function(_wF,_wG,_wH,_wI,_wJ){return new F(function(){return _wt(_wF,_wG,_wJ,_wH,_wI);});},_wK=function(_wL,_wM,_wN,_wO){var _wP=E(_wN);return new F(function(){return _wE(_wL,_wM,_wP[1],_wP[2],_wO);});},_wQ=function(_wR,_wS,_wT,_wU){return new F(function(){return _wK(_wU,_wT,_wS,_wR);});},_wV=new T(function(){return B(unCStr("Int"));}),_wW=function(_wX,_wY,_wZ){return new F(function(){return _wQ(_w7,[0,_wY,_wZ],_wX,_wV);});},_x0=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_x1=new T(function(){return B(err(_x0));}),_x2=1100,_x3=[0,_vo,_x2],_x4=function(_x5){return new F(function(){return _wQ(_w7,_x3,_x5,_wV);});},_x6=function(_){var _x7=newArr(1101,_x1),_x8=_x7,_x9=0;while(1){var _xa=B((function(_xb,_){if(0>_xb){return new F(function(){return _x4(_xb);});}else{if(_xb>1100){return new F(function(){return _x4(_xb);});}else{var _=_x8[_xb]=new T(function(){if(_xb>=0){var _xc=E(_xb);if(!_xc){return E(_q4);}else{return B(_te(_oe,_xc));}}else{return E(_ub);}}),_xd=E(_xb);if(_xd==1100){return [0,E(_vo),E(_x2),1101,_x8];}else{_x9=_xd+1|0;return null;}}}})(_x9,_));if(_xa!=null){return _xa;}}},_xe=function(_xf){var _xg=B(A(_xf,[_]));return E(_xg);},_xh=new T(function(){return B(_xe(_x6));}),_xi=[0,10],_xj=324,_xk=[0,_vo,_xj],_xl=function(_xm){return new F(function(){return _wQ(_w7,_xk,_xm,_wV);});},_xn=function(_){var _xo=newArr(325,_x1),_xp=_xo,_xq=0;while(1){var _xr=B((function(_xs,_){if(0>_xs){return new F(function(){return _xl(_xs);});}else{if(_xs>324){return new F(function(){return _xl(_xs);});}else{var _=_xp[_xs]=new T(function(){if(_xs>=0){var _xt=E(_xs);if(!_xt){return E(_q4);}else{return B(_te(_xi,_xt));}}else{return E(_ub);}}),_xu=E(_xs);if(_xu==324){return [0,E(_vo),E(_xj),325,_xp];}else{_xq=_xu+1|0;return null;}}}})(_xq,_));if(_xr!=null){return _xr;}}},_xv=new T(function(){return B(_xe(_xn));}),_xw=function(_xx,_xy){var _xz=function(_xA){if(!B(_jl(_xx,_xi))){if(_xy>=0){var _xB=E(_xy);if(!_xB){return E(_q4);}else{return new F(function(){return _te(_xx,_xB);});}}else{return E(_ub);}}else{if(_xy>324){if(_xy>=0){var _xC=E(_xy);if(!_xC){return E(_q4);}else{return new F(function(){return _te(_xx,_xC);});}}else{return E(_ub);}}else{var _xD=E(_xv),_xE=E(_xD[1]),_xF=E(_xD[2]);if(_xE>_xy){return new F(function(){return _wW(_xy,_xE,_xF);});}else{if(_xy>_xF){return new F(function(){return _wW(_xy,_xE,_xF);});}else{return E(_xD[4][_xy-_xE|0]);}}}}};if(!B(_jl(_xx,_oe))){return new F(function(){return _xz(_);});}else{if(_xy<0){return new F(function(){return _xz(_);});}else{if(_xy>1100){return new F(function(){return _xz(_);});}else{var _xG=E(_xh),_xH=E(_xG[1]),_xI=E(_xG[2]);if(_xH>_xy){return new F(function(){return _wW(_xy,_xH,_xI);});}else{if(_xy>_xI){return new F(function(){return _wW(_xy,_xH,_xI);});}else{return E(_xG[4][_xy-_xH|0]);}}}}}},_xJ=function(_xK){return E(E(_xK)[6]);},_xL=function(_xM){return E(E(_xM)[4]);},_xN=function(_xO){var _xP=E(_xO);if(!_xP[0]){return _xP[1];}else{return new F(function(){return I_toNumber(_xP[1]);});}},_xQ=function(_xR){return E(E(_xR)[3]);},_xS=function(_xT){return E(E(_xT)[5]);},_xU=[1,_vo,_3n],_xV=function(_xW,_xX){while(1){var _xY=E(_xW);if(!_xY[0]){var _xZ=E(_xY[1]);if(_xZ==(-2147483648)){_xW=[1,I_fromInt(-2147483648)];continue;}else{var _y0=E(_xX);if(!_y0[0]){return [0,quot(_xZ,_y0[1])];}else{_xW=[1,I_fromInt(_xZ)];_xX=_y0;continue;}}}else{var _y1=_xY[1],_y2=E(_xX);return (_y2[0]==0)?[0,I_toInt(I_quot(_y1,I_fromInt(_y2[1])))]:[1,I_quot(_y1,_y2[1])];}}},_y3=function(_y4,_y5,_y6){if(!B(A(_T,[B(_tm(B(_to(B(_vA(B(_vy(_y4)))))))),_y6,new T(function(){return B(A(_tw,[B(_vw(B(_vu(B(_vC(_y4)))))),_jO]));})]))){var _y7=new T(function(){return B(A(_xQ,[_y4,_y6]));}),_y8=new T(function(){return B(A(_xL,[_y4,_y6]));}),_y9=new T(function(){return E(B(A(_xS,[_y4,_y6]))[1])-E(_y8)|0;}),_ya=new T(function(){return B(A(_xJ,[_y4,_y6]));}),_yb=new T(function(){return E(E(_ya)[2]);}),_yc=new T(function(){var _yd=E(_yb),_ye=E(_y9)-_yd|0;if(_ye<=0){return [0,new T(function(){return E(E(_ya)[1]);}),_yd];}else{return [0,new T(function(){var _yf=B(_xw(_y7,_ye));if(!B(_jl(_yf,_jO))){return B(_xV(E(_ya)[1],_yf));}else{return E(_jg);}}),_yd+_ye|0];}}),_yg=new T(function(){return E(E(_yc)[2]);}),_yh=new T(function(){return E(E(_yc)[1]);}),_yi=new T(function(){var _yj=E(_yg);if(_yj<0){if(_yj<=E(_y9)){return [0,new T(function(){return B(_sY(_yh,_oe));}),new T(function(){return B(_sY(B(_xw(_y7, -_yj)),_oe));}),_iu,_iu];}else{if(!B(_jl(_yh,B(_xw(_y7,E(_y8)-1|0))))){return [0,new T(function(){return B(_sY(_yh,_oe));}),new T(function(){return B(_sY(B(_xw(_y7, -_yj)),_oe));}),_iu,_iu];}else{return [0,new T(function(){return B(_sY(B(_sY(_yh,_y7)),_oe));}),new T(function(){return B(_sY(B(_xw(_y7, -_yj+1|0)),_oe));}),_y7,_iu];}}}else{var _yk=new T(function(){return B(_xw(_y7,_yj));});if(!B(_jl(_yh,B(_xw(_y7,E(_y8)-1|0))))){return [0,new T(function(){return B(_sY(B(_sY(_yh,_yk)),_oe));}),_oe,_yk,_yk];}else{return [0,new T(function(){return B(_sY(B(_sY(B(_sY(_yh,_yk)),_y7)),_oe));}),new T(function(){return B(_sY(_oe,_y7));}),new T(function(){return B(_sY(_yk,_y7));}),_yk];}}}),_yl=new T(function(){return E(E(_yi)[2]);}),_ym=new T(function(){return E(E(_yi)[3]);}),_yn=new T(function(){return E(E(_yi)[1]);}),_yo=new T(function(){var _yp=new T(function(){return B(_jw(_yn,_ym));}),_yq=function(_yr){var _ys=(Math.log(B(_xN(B(_jw(_yh,_iu)))))+E(_yg)*Math.log(B(_xN(_y7))))/Math.log(B(_xN(_y5))),_yt=_ys&4294967295;return (_yt>=_ys)?E(_yt):_yt+1|0;},_yu=function(_yv){while(1){if(_yv<0){if(!B(_lx(B(_sY(B(_xw(_y5, -_yv)),_yp)),_yl))){var _yw=_yv+1|0;_yv=_yw;continue;}else{return E(_yv);}}else{if(!B(_lx(_yp,B(_sY(B(_xw(_y5,_yv)),_yl))))){var _yw=_yv+1|0;_yv=_yw;continue;}else{return E(_yv);}}}};if(!B(_jl(_y7,_oe))){return B(_yu(B(_yq(_))));}else{if(!B(_jl(_y5,_xi))){return B(_yu(B(_yq(_))));}else{var _yx=(E(_y8)-1|0)+E(_yb)|0;if(_yx<0){return B(_yu(quot(imul(_yx,8651)|0,28738)));}else{return B(_yu(quot(imul(_yx,8651)|0,28738)+1|0));}}}}),_yy=new T(function(){var _yz=E(_yo),_yA=function(_yB,_yC,_yD,_yE,_yF){while(1){var _yG=B((function(_yH,_yI,_yJ,_yK,_yL){if(!B(_jl(_yJ,_jO))){var _yM=B(_jF(B(_sY(_yI,_y5)),_yJ)),_yN=_yM[1],_yO=_yM[2],_yP=B(_sY(_yL,_y5)),_yQ=B(_sY(_yK,_y5));if(!B(_g9(_yO,_yP))){if(!B(_jV(B(_jw(_yO,_yQ)),_yJ))){var _yR=[1,_yN,_yH],_yS=_yJ;_yB=_yR;_yC=_yO;_yD=_yS;_yE=_yQ;_yF=_yP;return null;}else{return [1,new T(function(){return B(_jw(_yN,_iu));}),_yH];}}else{return (!B(_jV(B(_jw(_yO,_yQ)),_yJ)))?[1,_yN,_yH]:(!B(_g9(B(_sY(_yO,_oe)),_yJ)))?[1,new T(function(){return B(_jw(_yN,_iu));}),_yH]:[1,_yN,_yH];}}else{return E(_jg);}})(_yB,_yC,_yD,_yE,_yF));if(_yG!=null){return _yG;}}};if(_yz<0){var _yT=B(_xw(_y5, -_yz));return B(_1A(_sb,B(_cJ(B(_yA(_3n,B(_sY(_yn,_yT)),_yl,B(_sY(_ym,_yT)),B(_sY(E(_yi)[4],_yT)))),_3n))));}else{return B(_1A(_sb,B(_cJ(B(_yA(_3n,_yn,B(_sY(_yl,B(_xw(_y5,_yz)))),_ym,E(_yi)[4])),_3n))));}});return [0,_yy,_yo];}else{return [0,_xU,_vo];}},_yU=function(_yV){var _yW=E(_yV);return (_yW==1)?E(_xU):[1,_vo,new T(function(){return B(_yU(_yW-1|0));})];},_yX=function(_yY,_yZ){while(1){var _z0=E(_yZ);if(!_z0[0]){return true;}else{if(!B(A(_yY,[_z0[1]]))){return false;}else{_yZ=_z0[2];continue;}}}},_z1=function(_z2){return (E(_z2)%2==0)?true:false;},_z3=new T(function(){return B(unCStr("roundTo: bad Value"));}),_z4=new T(function(){return B(err(_z3));}),_z5=function(_z6){return (E(_z6)==0)?true:false;},_z7=function(_z8,_z9,_za){var _zb=new T(function(){return quot(E(_z8),2);}),_zc=function(_zd,_ze,_zf){var _zg=E(_zf);if(!_zg[0]){return [0,_vo,new T(function(){var _zh=E(_zd);if(0>=_zh){return [0];}else{return B(_yU(_zh));}})];}else{var _zi=_zg[1],_zj=_zg[2],_zk=E(_zd);if(!_zk){var _zl=E(_zi),_zm=E(_zb);return (_zl!=_zm)?[0,new T(function(){if(_zl<_zm){return E(_vo);}else{return E(_v9);}}),_3n]:(!E(_ze))?[0,new T(function(){if(_zl<_zm){return E(_vo);}else{return E(_v9);}}),_3n]:(!B(_yX(_z5,_zj)))?[0,new T(function(){if(_zl<_zm){return E(_vo);}else{return E(_v9);}}),_3n]:[0,_vo,_3n];}else{var _zn=B(_zc(_zk-1|0,new T(function(){return B(_z1(_zi));},1),_zj)),_zo=_zn[2],_zp=E(_zn[1])+E(_zi)|0;return (_zp!=E(_z8))?[0,_vo,[1,_zp,_zo]]:[0,_v9,[1,_vo,_zo]];}}},_zq=B(_zc(_z9,_v6,_za)),_zr=_zq[1],_zs=_zq[2];switch(E(_zr)){case 0:return [0,_zr,_zs];case 1:return [0,_v9,[1,_v9,_zs]];default:return E(_z4);}},_zt=function(_zu,_zv){var _zw=E(_zv);if(!_zw[0]){return [0,_3n,_3n];}else{var _zx=_zw[1],_zy=_zw[2],_zz=E(_zu);if(_zz==1){return [0,[1,_zx,_3n],_zy];}else{var _zA=new T(function(){var _zB=B(_zt(_zz-1|0,_zy));return [0,_zB[1],_zB[2]];});return [0,[1,_zx,new T(function(){return E(E(_zA)[1]);})],new T(function(){return E(E(_zA)[2]);})];}}},_zC=new T(function(){return B(unCStr("e0"));}),_zD=[1,_vF,_zC],_zE=function(_zF){var _zG=E(_zF);return (_zG==1)?E(_zD):[1,_vF,new T(function(){return B(_zE(_zG-1|0));})];},_zH=10,_zI=function(_zJ,_zK){var _zL=E(_zK);return (_zL[0]==0)?[0]:[1,_zJ,new T(function(){return B(_zI(_zL[1],_zL[2]));})];},_zM=new T(function(){return B(unCStr("init"));}),_zN=new T(function(){return B(_1q(_zM));}),_zO=function(_zP){return E(E(_zP)[12]);},_zQ=function(_zR){return E(E(_zR)[11]);},_zS=function(_zT){return E(E(_zT)[14]);},_zU=new T(function(){return B(unCStr("NaN"));}),_zV=new T(function(){return B(unCStr("-Infinity"));}),_zW=new T(function(){return B(unCStr("formatRealFloat/doFmt/FFExponent: []"));}),_zX=new T(function(){return B(err(_zW));}),_zY=new T(function(){return B(unCStr("Infinity"));}),_zZ=[1,_vE,_3n],_A0=101,_A1=new T(function(){return B(_vl("GHC\\Float.hs:594:12-70|(d : ds\')"));}),_A2=new T(function(){return B(unCStr("0.0e0"));}),_A3=function(_A4){return E(E(_A4)[4]);},_A5=45,_A6=function(_A7,_A8,_A9,_Aa,_Ab){if(!B(A(_zQ,[_A7,_Ab]))){var _Ac=new T(function(){return B(_vw(new T(function(){return B(_vu(new T(function(){return B(_vC(_A7));})));})));});if(!B(A(_zO,[_A7,_Ab]))){var _Ad=function(_Ae,_Af,_Ag){while(1){var _Ah=B((function(_Ai,_Aj,_Ak){switch(E(_Ai)){case 0:var _Al=E(_A9);if(!_Al[0]){var _Am=B(_1A(_vi,_Aj));if(!_Am[0]){return E(_zX);}else{var _An=_Am[2],_Ao=E(_Am[1]),_Ap=function(_Aq){var _Ar=E(_An);if(!_Ar[0]){var _As=new T(function(){return B(unAppCStr(".0e",new T(function(){return B(_83(0,E(_Ak)-1|0,_3n));})));});return [1,_Ao,_As];}else{var _At=new T(function(){var _Au=new T(function(){return B(unAppCStr("e",new T(function(){return B(_83(0,E(_Ak)-1|0,_3n));})));},1);return B(_16(_Ar,_Au));});return [1,_Ao,[1,_vE,_At]];}};if(E(_Ao)==48){if(!E(_An)[0]){return E(_A2);}else{return new F(function(){return _Ap(_);});}}else{return new F(function(){return _Ap(_);});}}}else{var _Av=new T(function(){var _Aw=E(_Al[1]);if(_Aw>1){return E(_Aw);}else{return E(_v9);}}),_Ax=function(_Ay){var _Az=new T(function(){var _AA=B(_z7(_zH,new T(function(){return E(_Av)+1|0;},1),_Aj));return [0,_AA[1],_AA[2]];}),_AB=new T(function(){return E(E(_Az)[1]);}),_AC=new T(function(){if(E(_AB)<=0){var _AD=B(_1A(_vi,E(_Az)[2]));if(!_AD[0]){return E(_A1);}else{return [0,_AD[1],_AD[2]];}}else{var _AE=E(E(_Az)[2]);if(!_AE[0]){return E(_zN);}else{var _AF=B(_1A(_vi,B(_zI(_AE[1],_AE[2]))));if(!_AF[0]){return E(_A1);}else{return [0,_AF[1],_AF[2]];}}}}),_AG=new T(function(){return B(_16(E(_AC)[2],[1,_A0,new T(function(){return B(_83(0,(E(_Ak)-1|0)+E(_AB)|0,_3n));})]));});return [1,new T(function(){return E(E(_AC)[1]);}),[1,_vE,_AG]];},_AH=E(_Aj);if(!_AH[0]){return new F(function(){return _Ax(_);});}else{if(!E(_AH[1])){if(!E(_AH[2])[0]){return [1,_vF,[1,_vE,new T(function(){var _AI=E(_Av);if(0>=_AI){return E(_zC);}else{return B(_zE(_AI));}})]];}else{return new F(function(){return _Ax(_);});}}else{return new F(function(){return _Ax(_);});}}}break;case 1:var _AJ=E(_A9);if(!_AJ[0]){var _AK=E(_Ak);if(_AK>0){return new F(function(){return _vH(_AK,_3n,new T(function(){return B(_1A(_vi,_Aj));},1));});}else{var _AL=new T(function(){var _AM= -_AK;if(0>=_AM){return B(_1A(_vi,_Aj));}else{var _AN=new T(function(){return B(_1A(_vi,_Aj));}),_AO=function(_AP){var _AQ=E(_AP);return (_AQ==1)?[1,_vF,_AN]:[1,_vF,new T(function(){return B(_AO(_AQ-1|0));})];};return B(_AO(_AM));}});return new F(function(){return unAppCStr("0.",_AL);});}}else{var _AR=_AJ[1],_AS=E(_Ak);if(_AS<0){var _AT=new T(function(){var _AU= -_AS;if(0>=_AU){var _AV=B(_z7(_zH,new T(function(){var _AW=E(_AR);if(_AW>0){return E(_AW);}else{return E(_vo);}},1),_Aj));return B(_vp(_AV[1],_AV[2]));}else{var _AX=function(_AY){var _AZ=E(_AY);return (_AZ==1)?[1,_vo,_Aj]:[1,_vo,new T(function(){return B(_AX(_AZ-1|0));})];},_B0=B(_z7(_zH,new T(function(){var _B1=E(_AR);if(_B1>0){return E(_B1);}else{return E(_vo);}},1),B(_AX(_AU))));return B(_vp(_B0[1],_B0[2]));}});return [1,new T(function(){return E(E(_AT)[1]);}),new T(function(){var _B2=E(E(_AT)[2]);if(!_B2[0]){if(!E(_Aa)){return [0];}else{return E(_zZ);}}else{return [1,_vE,_B2];}})];}else{var _B3=B(_z7(_zH,new T(function(){var _B4=E(_AR);if(_B4>0){return _B4+_AS|0;}else{return E(_AS);}},1),_Aj)),_B5=_B3[2],_B6=_AS+E(_B3[1])|0;if(_B6>0){var _B7=B(_zt(_B6,B(_1A(_vi,_B5)))),_B8=_B7[2],_B9=E(_B7[1]);if(!_B9[0]){return new F(function(){return _16(_vG,new T(function(){var _Ba=E(_B8);if(!_Ba[0]){if(!E(_Aa)){return [0];}else{return E(_zZ);}}else{return [1,_vE,_Ba];}},1));});}else{return new F(function(){return _16(_B9,new T(function(){var _Bb=E(_B8);if(!_Bb[0]){if(!E(_Aa)){return [0];}else{return E(_zZ);}}else{return [1,_vE,_Bb];}},1));});}}else{return new F(function(){return _16(_vG,new T(function(){var _Bc=B(_1A(_vi,_B5));if(!_Bc[0]){if(!E(_Aa)){return [0];}else{return E(_zZ);}}else{return [1,_vE,_Bc];}},1));});}}}break;default:var _Bd=E(_Ak);if(_Bd>=0){if(_Bd<=7){var _Be=_Aj;_Ae=_v3;_Af=_Be;_Ag=_Bd;return null;}else{var _Be=_Aj;_Ae=_v2;_Af=_Be;_Ag=_Bd;return null;}}else{var _Be=_Aj;_Ae=_v2;_Af=_Be;_Ag=_Bd;return null;}}})(_Ae,_Af,_Ag));if(_Ah!=null){return _Ah;}}},_Bf=function(_Bg){var _Bh=new T(function(){var _Bi=B(_y3(_A7,_xi,new T(function(){return B(A(_A3,[_Ac,_Ab]));})));return B(_Ad(_A8,_Bi[1],_Bi[2]));});return [1,_A5,_Bh];};if(!B(A(_ts,[B(_to(B(_vA(B(_vy(_A7)))))),_Ab,new T(function(){return B(A(_tw,[_Ac,_jO]));})]))){if(!B(A(_zS,[_A7,_Ab]))){var _Bj=B(_y3(_A7,_xi,_Ab));return new F(function(){return _Ad(_A8,_Bj[1],_Bj[2]);});}else{return new F(function(){return _Bf(_);});}}else{return new F(function(){return _Bf(_);});}}else{return (!B(A(_ts,[B(_to(B(_vA(B(_vy(_A7)))))),_Ab,new T(function(){return B(A(_tw,[_Ac,_jO]));})])))?E(_zY):E(_zV);}}else{return E(_zU);}},_Bk=function(_Bl){var _Bm=u_towupper(E(_Bl));if(_Bm>>>0>1114111){return new F(function(){return _v7(_Bm);});}else{return _Bm;}},_Bn=function(_Bo,_Bp,_Bq,_Br){var _Bs=u_iswupper(_Bo),_Bt=_Bs,_Bu=u_towlower(_Bo);if(_Bu>>>0>1114111){var _Bv=B(_v7(_Bu));}else{switch(_Bu){case 101:var _Bw=B(_A6(_v1,_v2,_Bp,_v5,_Br));break;case 102:if(!E(_Bq)){var _Bx=B(_A6(_v1,_v3,_Bp,_v5,_Br));}else{var _Bx=B(_A6(_v1,_v3,_Bp,_v6,_Br));}var _Bw=_Bx;break;case 103:if(!E(_Bq)){var _By=B(_A6(_v1,_v4,_Bp,_v5,_Br));}else{var _By=B(_A6(_v1,_v4,_Bp,_v6,_Br));}var _Bw=_By;break;default:var _Bw=E(_ig);}var _Bv=_Bw;}if(!E(_Bt)){var _Bz=E(_Bv);return (_Bz[0]==0)?[0,_3n,_3n]:(E(_Bz[1])==45)?[0,_ie,_Bz[2]]:[0,_3n,_Bz];}else{var _BA=B(_1A(_Bk,_Bv));return (_BA[0]==0)?[0,_3n,_3n]:(E(_BA[1])==45)?[0,_ie,_BA[2]]:[0,_3n,_BA];}},_BB=new T(function(){return B(unCStr(" "));}),_BC=new T(function(){return B(unCStr("+"));}),_BD=48,_BE=32,_BF=function(_BG,_BH,_BI,_BJ){var _BK=new T(function(){var _BL=E(_BH);if(!_BL[0]){return false;}else{if(!E(_BL[1])){return false;}else{return true;}}}),_BM=new T(function(){var _BN=E(_BG);if(!_BN[0]){return [0];}else{var _BO=E(_BN[1]),_BP=B(_bb(_BI,0))+B(_bb(_BJ,0))|0;if(_BP>=_BO){return [0];}else{var _BQ=_BO-_BP|0;if(0>=_BQ){return [0];}else{var _BR=new T(function(){if(!E(_BK)){return E(_BE);}else{return E(_BD);}}),_BS=function(_BT){var _BU=E(_BT);return (_BU==1)?[1,_BR,_3n]:[1,_BR,new T(function(){return B(_BS(_BU-1|0));})];};return B(_BS(_BQ));}}}}),_BV=function(_BW){if(!E(_BK)){return new F(function(){return _16(_BM,new T(function(){return B(_16(_BI,_BJ));},1));});}else{return new F(function(){return _16(_BI,new T(function(){return B(_16(_BM,_BJ));},1));});}},_BX=E(_BH);if(!_BX[0]){return new F(function(){return _BV(_);});}else{if(!E(_BX[1])){return new F(function(){return _16(_BI,new T(function(){return B(_16(_BJ,_BM));},1));});}else{return new F(function(){return _BV(_);});}}},_BY=function(_BZ,_C0,_C1,_C2,_C3){var _C4=E(_C1);if(!_C4[0]){return new F(function(){return _BF(_BZ,_C0,_C2,_C3);});}else{if(!E(_C4[1])){var _C5=E(_C2);if(!_C5[0]){return new F(function(){return _BF(_BZ,_C0,_BC,_C3);});}else{return new F(function(){return _BF(_BZ,_C0,_C5,_C3);});}}else{var _C6=E(_C2);if(!_C6[0]){return new F(function(){return _BF(_BZ,_C0,_BB,_C3);});}else{return new F(function(){return _BF(_BZ,_C0,_C6,_C3);});}}}},_C7=function(_C8,_C9,_Ca,_Cb,_Cc,_Cd,_Ce){var _Cf=E(_Ce);switch(_Cf){case 69:var _Cg=new T(function(){var _Ch=B(_Bn(69,_Ca,_Cd,_C8));return B(_BY(_C9,_Cb,_Cc,_Ch[1],_Ch[2]));});return function(_Ci){return new F(function(){return _16(_Cg,_Ci);});};case 70:var _Cj=new T(function(){var _Ck=B(_Bn(70,_Ca,_Cd,_C8));return B(_BY(_C9,_Cb,_Cc,_Ck[1],_Ck[2]));});return function(_Ci){return new F(function(){return _16(_Cj,_Ci);});};case 71:var _Cl=new T(function(){var _Cm=B(_Bn(71,_Ca,_Cd,_C8));return B(_BY(_C9,_Cb,_Cc,_Cm[1],_Cm[2]));});return function(_Ci){return new F(function(){return _16(_Cl,_Ci);});};case 101:var _Cn=new T(function(){var _Co=B(_Bn(101,_Ca,_Cd,_C8));return B(_BY(_C9,_Cb,_Cc,_Co[1],_Co[2]));});return function(_Ci){return new F(function(){return _16(_Cn,_Ci);});};case 102:var _Cp=new T(function(){var _Cq=B(_Bn(102,_Ca,_Cd,_C8));return B(_BY(_C9,_Cb,_Cc,_Cq[1],_Cq[2]));});return function(_Ci){return new F(function(){return _16(_Cp,_Ci);});};case 103:var _Cr=new T(function(){var _Cs=B(_Bn(103,_Ca,_Cd,_C8));return B(_BY(_C9,_Cb,_Cc,_Cs[1],_Cs[2]));});return function(_Ci){return new F(function(){return _16(_Cr,_Ci);});};case 118:var _Ct=new T(function(){var _Cu=B(_Bn(103,_Ca,_Cd,_C8));return B(_BY(_C9,_Cb,_Cc,_Cu[1],_Cu[2]));});return function(_Ci){return new F(function(){return _16(_Ct,_Ci);});};default:return new F(function(){return _i9(_Cf);});}},_Cv=function(_Cw,_Cx){var _Cy=E(_Cx);return new F(function(){return _C7(_Cw,_Cy[1],_Cy[2],_Cy[3],_Cy[4],_Cy[5],E(_Cy[7]));});},_Cz=function(_CA){return E(_CA);},_CB=new T(function(){return B(unCStr("printf: argument list ended prematurely"));}),_CC=new T(function(){return B(err(_CB));}),_CD=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_CE=new T(function(){return B(err(_CD));}),_CF=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_CG=new T(function(){return B(err(_CF));}),_CH=new T(function(){return B(_kZ("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_CI=function(_CJ,_CK){while(1){var _CL=B((function(_CM,_CN){var _CO=E(_CM);switch(_CO[0]){case 0:var _CP=E(_CN);if(!_CP[0]){return [0];}else{_CJ=B(A(_CO[1],[_CP[1]]));_CK=_CP[2];return null;}break;case 1:var _CQ=B(A(_CO[1],[_CN])),_CR=_CN;_CJ=_CQ;_CK=_CR;return null;case 2:return [0];case 3:return [1,[0,_CO[1],_CN],new T(function(){return B(_CI(_CO[2],_CN));})];default:return E(_CO[1]);}})(_CJ,_CK));if(_CL!=null){return _CL;}}},_CS=function(_CT,_CU){var _CV=function(_CW){var _CX=E(_CU);if(_CX[0]==3){return [3,_CX[1],new T(function(){return B(_CS(_CT,_CX[2]));})];}else{var _CY=E(_CT);if(_CY[0]==2){return E(_CX);}else{var _CZ=E(_CX);if(_CZ[0]==2){return E(_CY);}else{var _D0=function(_D1){var _D2=E(_CZ);if(_D2[0]==4){return [1,function(_D3){return [4,new T(function(){return B(_16(B(_CI(_CY,_D3)),_D2[1]));})];}];}else{var _D4=E(_CY);if(_D4[0]==1){var _D5=_D4[1],_D6=E(_D2);if(!_D6[0]){return [1,function(_D7){return new F(function(){return _CS(B(A(_D5,[_D7])),_D6);});}];}else{return [1,function(_D8){return new F(function(){return _CS(B(A(_D5,[_D8])),new T(function(){return B(A(_D6[1],[_D8]));}));});}];}}else{var _D9=E(_D2);if(!_D9[0]){return E(_CH);}else{return [1,function(_Da){return new F(function(){return _CS(_D4,new T(function(){return B(A(_D9[1],[_Da]));}));});}];}}}},_Db=E(_CY);switch(_Db[0]){case 1:var _Dc=E(_CZ);if(_Dc[0]==4){return [1,function(_Dd){return [4,new T(function(){return B(_16(B(_CI(B(A(_Db[1],[_Dd])),_Dd)),_Dc[1]));})];}];}else{return new F(function(){return _D0(_);});}break;case 4:var _De=_Db[1],_Df=E(_CZ);switch(_Df[0]){case 0:return [1,function(_Dg){return [4,new T(function(){return B(_16(_De,new T(function(){return B(_CI(_Df,_Dg));},1)));})];}];case 1:return [1,function(_Dh){return [4,new T(function(){return B(_16(_De,new T(function(){return B(_CI(B(A(_Df[1],[_Dh])),_Dh));},1)));})];}];default:return [4,new T(function(){return B(_16(_De,_Df[1]));})];}break;default:return new F(function(){return _D0(_);});}}}}},_Di=E(_CT);switch(_Di[0]){case 0:var _Dj=E(_CU);if(!_Dj[0]){return [0,function(_Dk){return new F(function(){return _CS(B(A(_Di[1],[_Dk])),new T(function(){return B(A(_Dj[1],[_Dk]));}));});}];}else{return new F(function(){return _CV(_);});}break;case 3:return [3,_Di[1],new T(function(){return B(_CS(_Di[2],_CU));})];default:return new F(function(){return _CV(_);});}},_Dl=new T(function(){return B(unCStr("("));}),_Dm=new T(function(){return B(unCStr(")"));}),_Dn=function(_Do,_Dp){return E(_Do)!=E(_Dp);},_Dq=function(_Dr,_Ds){return E(_Dr)==E(_Ds);},_Dt=[0,_Dq,_Dn],_Du=function(_Dv,_Dw){while(1){var _Dx=E(_Dv);if(!_Dx[0]){return (E(_Dw)[0]==0)?true:false;}else{var _Dy=E(_Dw);if(!_Dy[0]){return false;}else{if(E(_Dx[1])!=E(_Dy[1])){return false;}else{_Dv=_Dx[2];_Dw=_Dy[2];continue;}}}}},_Dz=function(_DA,_DB){return (!B(_Du(_DA,_DB)))?true:false;},_DC=[0,_Du,_Dz],_DD=function(_DE,_DF){var _DG=E(_DE);switch(_DG[0]){case 0:return [0,function(_DH){return new F(function(){return _DD(B(A(_DG[1],[_DH])),_DF);});}];case 1:return [1,function(_DI){return new F(function(){return _DD(B(A(_DG[1],[_DI])),_DF);});}];case 2:return [2];case 3:return new F(function(){return _CS(B(A(_DF,[_DG[1]])),new T(function(){return B(_DD(_DG[2],_DF));}));});break;default:var _DJ=function(_DK){var _DL=E(_DK);if(!_DL[0]){return [0];}else{var _DM=E(_DL[1]);return new F(function(){return _16(B(_CI(B(A(_DF,[_DM[1]])),_DM[2])),new T(function(){return B(_DJ(_DL[2]));},1));});}},_DN=B(_DJ(_DG[1]));return (_DN[0]==0)?[2]:[4,_DN];}},_DO=[2],_DP=function(_DQ){return [3,_DQ,_DO];},_DR=function(_DS,_DT){var _DU=E(_DS);if(!_DU){return new F(function(){return A(_DT,[_a]);});}else{var _DV=new T(function(){return B(_DR(_DU-1|0,_DT));});return [0,function(_DW){return E(_DV);}];}},_DX=function(_DY,_DZ,_E0){var _E1=new T(function(){return B(A(_DY,[_DP]));}),_E2=function(_E3,_E4,_E5,_E6){while(1){var _E7=B((function(_E8,_E9,_Ea,_Eb){var _Ec=E(_E8);switch(_Ec[0]){case 0:var _Ed=E(_E9);if(!_Ed[0]){return new F(function(){return A(_DZ,[_Eb]);});}else{var _Ee=_Ea+1|0,_Ef=_Eb;_E3=B(A(_Ec[1],[_Ed[1]]));_E4=_Ed[2];_E5=_Ee;_E6=_Ef;return null;}break;case 1:var _Eg=B(A(_Ec[1],[_E9])),_Eh=_E9,_Ee=_Ea,_Ef=_Eb;_E3=_Eg;_E4=_Eh;_E5=_Ee;_E6=_Ef;return null;case 2:return new F(function(){return A(_DZ,[_Eb]);});break;case 3:var _Ei=new T(function(){return B(_DD(_Ec,_Eb));});return new F(function(){return _DR(_Ea,function(_Ej){return E(_Ei);});});break;default:return new F(function(){return _DD(_Ec,_Eb);});}})(_E3,_E4,_E5,_E6));if(_E7!=null){return _E7;}}};return function(_Ek){return new F(function(){return _E2(_E1,_Ek,0,_E0);});};},_El=function(_Em){return new F(function(){return A(_Em,[_3n]);});},_En=function(_Eo,_Ep){var _Eq=function(_Er){var _Es=E(_Er);if(!_Es[0]){return E(_El);}else{var _Et=_Es[1];if(!B(A(_Eo,[_Et]))){return E(_El);}else{var _Eu=new T(function(){return B(_Eq(_Es[2]));}),_Ev=function(_Ew){var _Ex=new T(function(){return B(A(_Eu,[function(_Ey){return new F(function(){return A(_Ew,[[1,_Et,_Ey]]);});}]));});return [0,function(_Ez){return E(_Ex);}];};return E(_Ev);}}};return function(_EA){return new F(function(){return A(_Eq,[_EA,_Ep]);});};},_EB=[6],_EC=new T(function(){return B(unCStr("valDig: Bad base"));}),_ED=new T(function(){return B(err(_EC));}),_EE=function(_EF,_EG){var _EH=function(_EI,_EJ){var _EK=E(_EI);if(!_EK[0]){var _EL=new T(function(){return B(A(_EJ,[_3n]));});return function(_EM){return new F(function(){return A(_EM,[_EL]);});};}else{var _EN=E(_EK[1]),_EO=function(_EP){var _EQ=new T(function(){return B(_EH(_EK[2],function(_ER){return new F(function(){return A(_EJ,[[1,_EP,_ER]]);});}));}),_ES=function(_ET){var _EU=new T(function(){return B(A(_EQ,[_ET]));});return [0,function(_EV){return E(_EU);}];};return E(_ES);};switch(E(_EF)){case 8:if(48>_EN){var _EW=new T(function(){return B(A(_EJ,[_3n]));});return function(_EX){return new F(function(){return A(_EX,[_EW]);});};}else{if(_EN>55){var _EY=new T(function(){return B(A(_EJ,[_3n]));});return function(_EZ){return new F(function(){return A(_EZ,[_EY]);});};}else{return new F(function(){return _EO(_EN-48|0);});}}break;case 10:if(48>_EN){var _F0=new T(function(){return B(A(_EJ,[_3n]));});return function(_F1){return new F(function(){return A(_F1,[_F0]);});};}else{if(_EN>57){var _F2=new T(function(){return B(A(_EJ,[_3n]));});return function(_F3){return new F(function(){return A(_F3,[_F2]);});};}else{return new F(function(){return _EO(_EN-48|0);});}}break;case 16:if(48>_EN){if(97>_EN){if(65>_EN){var _F4=new T(function(){return B(A(_EJ,[_3n]));});return function(_F5){return new F(function(){return A(_F5,[_F4]);});};}else{if(_EN>70){var _F6=new T(function(){return B(A(_EJ,[_3n]));});return function(_F7){return new F(function(){return A(_F7,[_F6]);});};}else{return new F(function(){return _EO((_EN-65|0)+10|0);});}}}else{if(_EN>102){if(65>_EN){var _F8=new T(function(){return B(A(_EJ,[_3n]));});return function(_F9){return new F(function(){return A(_F9,[_F8]);});};}else{if(_EN>70){var _Fa=new T(function(){return B(A(_EJ,[_3n]));});return function(_Fb){return new F(function(){return A(_Fb,[_Fa]);});};}else{return new F(function(){return _EO((_EN-65|0)+10|0);});}}}else{return new F(function(){return _EO((_EN-97|0)+10|0);});}}}else{if(_EN>57){if(97>_EN){if(65>_EN){var _Fc=new T(function(){return B(A(_EJ,[_3n]));});return function(_Fd){return new F(function(){return A(_Fd,[_Fc]);});};}else{if(_EN>70){var _Fe=new T(function(){return B(A(_EJ,[_3n]));});return function(_Ff){return new F(function(){return A(_Ff,[_Fe]);});};}else{return new F(function(){return _EO((_EN-65|0)+10|0);});}}}else{if(_EN>102){if(65>_EN){var _Fg=new T(function(){return B(A(_EJ,[_3n]));});return function(_Fh){return new F(function(){return A(_Fh,[_Fg]);});};}else{if(_EN>70){var _Fi=new T(function(){return B(A(_EJ,[_3n]));});return function(_Fj){return new F(function(){return A(_Fj,[_Fi]);});};}else{return new F(function(){return _EO((_EN-65|0)+10|0);});}}}else{return new F(function(){return _EO((_EN-97|0)+10|0);});}}}else{return new F(function(){return _EO(_EN-48|0);});}}break;default:return E(_ED);}}},_Fk=function(_Fl){var _Fm=E(_Fl);if(!_Fm[0]){return [2];}else{return new F(function(){return A(_EG,[_Fm]);});}};return function(_Fn){return new F(function(){return A(_EH,[_Fn,_Q,_Fk]);});};},_Fo=16,_Fp=8,_Fq=function(_Fr){var _Fs=function(_Ft){return new F(function(){return A(_Fr,[[5,[0,_Fp,_Ft]]]);});},_Fu=function(_Fv){return new F(function(){return A(_Fr,[[5,[0,_Fo,_Fv]]]);});},_Fw=function(_Fx){switch(E(_Fx)){case 79:return [1,B(_EE(_Fp,_Fs))];case 88:return [1,B(_EE(_Fo,_Fu))];case 111:return [1,B(_EE(_Fp,_Fs))];case 120:return [1,B(_EE(_Fo,_Fu))];default:return [2];}};return function(_Fy){return (E(_Fy)==48)?[0,_Fw]:[2];};},_Fz=function(_FA){return [0,B(_Fq(_FA))];},_FB=function(_FC){return new F(function(){return A(_FC,[_6C]);});},_FD=function(_FE){return new F(function(){return A(_FE,[_6C]);});},_FF=10,_FG=[0,10],_FH=function(_FI){return new F(function(){return _bO(E(_FI));});},_FJ=new T(function(){return B(unCStr("this should not happen"));}),_FK=new T(function(){return B(err(_FJ));}),_FL=function(_FM,_FN){var _FO=E(_FN);if(!_FO[0]){return [0];}else{var _FP=E(_FO[2]);return (_FP[0]==0)?E(_FK):[1,B(_jw(B(_sY(_FO[1],_FM)),_FP[1])),new T(function(){return B(_FL(_FM,_FP[2]));})];}},_FQ=[0,0],_FR=function(_FS,_FT,_FU){while(1){var _FV=B((function(_FW,_FX,_FY){var _FZ=E(_FY);if(!_FZ[0]){return E(_FQ);}else{if(!E(_FZ[2])[0]){return E(_FZ[1]);}else{var _G0=E(_FX);if(_G0<=40){var _G1=_FQ,_G2=_FZ;while(1){var _G3=E(_G2);if(!_G3[0]){return E(_G1);}else{var _G4=B(_jw(B(_sY(_G1,_FW)),_G3[1]));_G1=_G4;_G2=_G3[2];continue;}}}else{var _G5=B(_sY(_FW,_FW));if(!(_G0%2)){var _G6=B(_FL(_FW,_FZ));_FS=_G5;_FT=quot(_G0+1|0,2);_FU=_G6;return null;}else{var _G6=B(_FL(_FW,[1,_FQ,_FZ]));_FS=_G5;_FT=quot(_G0+1|0,2);_FU=_G6;return null;}}}}})(_FS,_FT,_FU));if(_FV!=null){return _FV;}}},_G7=function(_G8,_G9){return new F(function(){return _FR(_G8,new T(function(){return B(_bb(_G9,0));},1),B(_1A(_FH,_G9)));});},_Ga=function(_Gb){var _Gc=new T(function(){var _Gd=new T(function(){var _Ge=function(_Gf){return new F(function(){return A(_Gb,[[1,new T(function(){return B(_G7(_FG,_Gf));})]]);});};return [1,B(_EE(_FF,_Ge))];}),_Gg=function(_Gh){if(E(_Gh)==43){var _Gi=function(_Gj){return new F(function(){return A(_Gb,[[1,new T(function(){return B(_G7(_FG,_Gj));})]]);});};return [1,B(_EE(_FF,_Gi))];}else{return [2];}},_Gk=function(_Gl){if(E(_Gl)==45){var _Gm=function(_Gn){return new F(function(){return A(_Gb,[[1,new T(function(){return B(_mr(B(_G7(_FG,_Gn))));})]]);});};return [1,B(_EE(_FF,_Gm))];}else{return [2];}};return B(_CS(B(_CS([0,_Gk],[0,_Gg])),_Gd));});return new F(function(){return _CS([0,function(_Go){return (E(_Go)==101)?E(_Gc):[2];}],[0,function(_Gp){return (E(_Gp)==69)?E(_Gc):[2];}]);});},_Gq=function(_Gr){var _Gs=function(_Gt){return new F(function(){return A(_Gr,[[1,_Gt]]);});};return function(_Gu){return (E(_Gu)==46)?[1,B(_EE(_FF,_Gs))]:[2];};},_Gv=function(_Gw){return [0,B(_Gq(_Gw))];},_Gx=function(_Gy){var _Gz=function(_GA){var _GB=function(_GC){return [1,B(_DX(_Ga,_FB,function(_GD){return new F(function(){return A(_Gy,[[5,[1,_GA,_GC,_GD]]]);});}))];};return [1,B(_DX(_Gv,_FD,_GB))];};return new F(function(){return _EE(_FF,_Gz);});},_GE=function(_GF){return [1,B(_Gx(_GF))];},_GG=function(_GH,_GI,_GJ){while(1){var _GK=E(_GJ);if(!_GK[0]){return false;}else{if(!B(A(_T,[_GH,_GI,_GK[1]]))){_GJ=_GK[2];continue;}else{return true;}}}},_GL=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_GM=function(_GN){return new F(function(){return _GG(_Dt,_GN,_GL);});},_GO=function(_GP){var _GQ=new T(function(){return B(A(_GP,[_Fp]));}),_GR=new T(function(){return B(A(_GP,[_Fo]));});return function(_GS){switch(E(_GS)){case 79:return E(_GQ);case 88:return E(_GR);case 111:return E(_GQ);case 120:return E(_GR);default:return [2];}};},_GT=function(_GU){return [0,B(_GO(_GU))];},_GV=function(_GW){return new F(function(){return A(_GW,[_FF]);});},_GX=function(_GY){return [2];},_GZ=function(_H0){var _H1=E(_H0);if(!_H1[0]){return E(_GX);}else{var _H2=_H1[1],_H3=E(_H1[2]);if(!_H3[0]){return E(_H2);}else{var _H4=new T(function(){return B(_GZ(_H3));}),_H5=function(_H6){return new F(function(){return _CS(B(A(_H2,[_H6])),new T(function(){return B(A(_H4,[_H6]));}));});};return E(_H5);}}},_H7=function(_H8,_H9){var _Ha=function(_Hb,_Hc,_Hd){var _He=E(_Hb);if(!_He[0]){return new F(function(){return A(_Hd,[_H8]);});}else{var _Hf=E(_Hc);if(!_Hf[0]){return [2];}else{if(E(_He[1])!=E(_Hf[1])){return [2];}else{var _Hg=new T(function(){return B(_Ha(_He[2],_Hf[2],_Hd));});return [0,function(_Hh){return E(_Hg);}];}}}};return function(_Hi){return new F(function(){return _Ha(_H8,_Hi,_H9);});};},_Hj=new T(function(){return B(unCStr("SO"));}),_Hk=14,_Hl=function(_Hm){var _Hn=new T(function(){return B(A(_Hm,[_Hk]));});return [1,B(_H7(_Hj,function(_Ho){return E(_Hn);}))];},_Hp=new T(function(){return B(unCStr("SOH"));}),_Hq=1,_Hr=function(_Hs){var _Ht=new T(function(){return B(A(_Hs,[_Hq]));});return [1,B(_H7(_Hp,function(_Hu){return E(_Ht);}))];},_Hv=function(_Hw){return [1,B(_DX(_Hr,_Hl,_Hw))];},_Hx=new T(function(){return B(unCStr("NUL"));}),_Hy=0,_Hz=function(_HA){var _HB=new T(function(){return B(A(_HA,[_Hy]));});return [1,B(_H7(_Hx,function(_HC){return E(_HB);}))];},_HD=new T(function(){return B(unCStr("STX"));}),_HE=2,_HF=function(_HG){var _HH=new T(function(){return B(A(_HG,[_HE]));});return [1,B(_H7(_HD,function(_HI){return E(_HH);}))];},_HJ=new T(function(){return B(unCStr("ETX"));}),_HK=3,_HL=function(_HM){var _HN=new T(function(){return B(A(_HM,[_HK]));});return [1,B(_H7(_HJ,function(_HO){return E(_HN);}))];},_HP=new T(function(){return B(unCStr("EOT"));}),_HQ=4,_HR=function(_HS){var _HT=new T(function(){return B(A(_HS,[_HQ]));});return [1,B(_H7(_HP,function(_HU){return E(_HT);}))];},_HV=new T(function(){return B(unCStr("ENQ"));}),_HW=5,_HX=function(_HY){var _HZ=new T(function(){return B(A(_HY,[_HW]));});return [1,B(_H7(_HV,function(_I0){return E(_HZ);}))];},_I1=new T(function(){return B(unCStr("ACK"));}),_I2=6,_I3=function(_I4){var _I5=new T(function(){return B(A(_I4,[_I2]));});return [1,B(_H7(_I1,function(_I6){return E(_I5);}))];},_I7=new T(function(){return B(unCStr("BEL"));}),_I8=7,_I9=function(_Ia){var _Ib=new T(function(){return B(A(_Ia,[_I8]));});return [1,B(_H7(_I7,function(_Ic){return E(_Ib);}))];},_Id=new T(function(){return B(unCStr("BS"));}),_Ie=8,_If=function(_Ig){var _Ih=new T(function(){return B(A(_Ig,[_Ie]));});return [1,B(_H7(_Id,function(_Ii){return E(_Ih);}))];},_Ij=new T(function(){return B(unCStr("HT"));}),_Ik=9,_Il=function(_Im){var _In=new T(function(){return B(A(_Im,[_Ik]));});return [1,B(_H7(_Ij,function(_Io){return E(_In);}))];},_Ip=new T(function(){return B(unCStr("LF"));}),_Iq=10,_Ir=function(_Is){var _It=new T(function(){return B(A(_Is,[_Iq]));});return [1,B(_H7(_Ip,function(_Iu){return E(_It);}))];},_Iv=new T(function(){return B(unCStr("VT"));}),_Iw=11,_Ix=function(_Iy){var _Iz=new T(function(){return B(A(_Iy,[_Iw]));});return [1,B(_H7(_Iv,function(_IA){return E(_Iz);}))];},_IB=new T(function(){return B(unCStr("FF"));}),_IC=12,_ID=function(_IE){var _IF=new T(function(){return B(A(_IE,[_IC]));});return [1,B(_H7(_IB,function(_IG){return E(_IF);}))];},_IH=new T(function(){return B(unCStr("CR"));}),_II=13,_IJ=function(_IK){var _IL=new T(function(){return B(A(_IK,[_II]));});return [1,B(_H7(_IH,function(_IM){return E(_IL);}))];},_IN=new T(function(){return B(unCStr("SI"));}),_IO=15,_IP=function(_IQ){var _IR=new T(function(){return B(A(_IQ,[_IO]));});return [1,B(_H7(_IN,function(_IS){return E(_IR);}))];},_IT=new T(function(){return B(unCStr("DLE"));}),_IU=16,_IV=function(_IW){var _IX=new T(function(){return B(A(_IW,[_IU]));});return [1,B(_H7(_IT,function(_IY){return E(_IX);}))];},_IZ=new T(function(){return B(unCStr("DC1"));}),_J0=17,_J1=function(_J2){var _J3=new T(function(){return B(A(_J2,[_J0]));});return [1,B(_H7(_IZ,function(_J4){return E(_J3);}))];},_J5=new T(function(){return B(unCStr("DC2"));}),_J6=18,_J7=function(_J8){var _J9=new T(function(){return B(A(_J8,[_J6]));});return [1,B(_H7(_J5,function(_Ja){return E(_J9);}))];},_Jb=new T(function(){return B(unCStr("DC3"));}),_Jc=19,_Jd=function(_Je){var _Jf=new T(function(){return B(A(_Je,[_Jc]));});return [1,B(_H7(_Jb,function(_Jg){return E(_Jf);}))];},_Jh=new T(function(){return B(unCStr("DC4"));}),_Ji=20,_Jj=function(_Jk){var _Jl=new T(function(){return B(A(_Jk,[_Ji]));});return [1,B(_H7(_Jh,function(_Jm){return E(_Jl);}))];},_Jn=new T(function(){return B(unCStr("NAK"));}),_Jo=21,_Jp=function(_Jq){var _Jr=new T(function(){return B(A(_Jq,[_Jo]));});return [1,B(_H7(_Jn,function(_Js){return E(_Jr);}))];},_Jt=new T(function(){return B(unCStr("SYN"));}),_Ju=22,_Jv=function(_Jw){var _Jx=new T(function(){return B(A(_Jw,[_Ju]));});return [1,B(_H7(_Jt,function(_Jy){return E(_Jx);}))];},_Jz=new T(function(){return B(unCStr("ETB"));}),_JA=23,_JB=function(_JC){var _JD=new T(function(){return B(A(_JC,[_JA]));});return [1,B(_H7(_Jz,function(_JE){return E(_JD);}))];},_JF=new T(function(){return B(unCStr("CAN"));}),_JG=24,_JH=function(_JI){var _JJ=new T(function(){return B(A(_JI,[_JG]));});return [1,B(_H7(_JF,function(_JK){return E(_JJ);}))];},_JL=new T(function(){return B(unCStr("EM"));}),_JM=25,_JN=function(_JO){var _JP=new T(function(){return B(A(_JO,[_JM]));});return [1,B(_H7(_JL,function(_JQ){return E(_JP);}))];},_JR=new T(function(){return B(unCStr("SUB"));}),_JS=26,_JT=function(_JU){var _JV=new T(function(){return B(A(_JU,[_JS]));});return [1,B(_H7(_JR,function(_JW){return E(_JV);}))];},_JX=new T(function(){return B(unCStr("ESC"));}),_JY=27,_JZ=function(_K0){var _K1=new T(function(){return B(A(_K0,[_JY]));});return [1,B(_H7(_JX,function(_K2){return E(_K1);}))];},_K3=new T(function(){return B(unCStr("FS"));}),_K4=28,_K5=function(_K6){var _K7=new T(function(){return B(A(_K6,[_K4]));});return [1,B(_H7(_K3,function(_K8){return E(_K7);}))];},_K9=new T(function(){return B(unCStr("GS"));}),_Ka=29,_Kb=function(_Kc){var _Kd=new T(function(){return B(A(_Kc,[_Ka]));});return [1,B(_H7(_K9,function(_Ke){return E(_Kd);}))];},_Kf=new T(function(){return B(unCStr("RS"));}),_Kg=30,_Kh=function(_Ki){var _Kj=new T(function(){return B(A(_Ki,[_Kg]));});return [1,B(_H7(_Kf,function(_Kk){return E(_Kj);}))];},_Kl=new T(function(){return B(unCStr("US"));}),_Km=31,_Kn=function(_Ko){var _Kp=new T(function(){return B(A(_Ko,[_Km]));});return [1,B(_H7(_Kl,function(_Kq){return E(_Kp);}))];},_Kr=new T(function(){return B(unCStr("SP"));}),_Ks=32,_Kt=function(_Ku){var _Kv=new T(function(){return B(A(_Ku,[_Ks]));});return [1,B(_H7(_Kr,function(_Kw){return E(_Kv);}))];},_Kx=new T(function(){return B(unCStr("DEL"));}),_Ky=127,_Kz=function(_KA){var _KB=new T(function(){return B(A(_KA,[_Ky]));});return [1,B(_H7(_Kx,function(_KC){return E(_KB);}))];},_KD=[1,_Kz,_3n],_KE=[1,_Kt,_KD],_KF=[1,_Kn,_KE],_KG=[1,_Kh,_KF],_KH=[1,_Kb,_KG],_KI=[1,_K5,_KH],_KJ=[1,_JZ,_KI],_KK=[1,_JT,_KJ],_KL=[1,_JN,_KK],_KM=[1,_JH,_KL],_KN=[1,_JB,_KM],_KO=[1,_Jv,_KN],_KP=[1,_Jp,_KO],_KQ=[1,_Jj,_KP],_KR=[1,_Jd,_KQ],_KS=[1,_J7,_KR],_KT=[1,_J1,_KS],_KU=[1,_IV,_KT],_KV=[1,_IP,_KU],_KW=[1,_IJ,_KV],_KX=[1,_ID,_KW],_KY=[1,_Ix,_KX],_KZ=[1,_Ir,_KY],_L0=[1,_Il,_KZ],_L1=[1,_If,_L0],_L2=[1,_I9,_L1],_L3=[1,_I3,_L2],_L4=[1,_HX,_L3],_L5=[1,_HR,_L4],_L6=[1,_HL,_L5],_L7=[1,_HF,_L6],_L8=[1,_Hz,_L7],_L9=[1,_Hv,_L8],_La=new T(function(){return B(_GZ(_L9));}),_Lb=34,_Lc=[0,1114111],_Ld=92,_Le=39,_Lf=function(_Lg){var _Lh=new T(function(){return B(A(_Lg,[_I8]));}),_Li=new T(function(){return B(A(_Lg,[_Ie]));}),_Lj=new T(function(){return B(A(_Lg,[_Ik]));}),_Lk=new T(function(){return B(A(_Lg,[_Iq]));}),_Ll=new T(function(){return B(A(_Lg,[_Iw]));}),_Lm=new T(function(){return B(A(_Lg,[_IC]));}),_Ln=new T(function(){return B(A(_Lg,[_II]));}),_Lo=new T(function(){return B(A(_Lg,[_Ld]));}),_Lp=new T(function(){return B(A(_Lg,[_Le]));}),_Lq=new T(function(){return B(A(_Lg,[_Lb]));}),_Lr=new T(function(){var _Ls=function(_Lt){var _Lu=new T(function(){return B(_bO(E(_Lt)));}),_Lv=function(_Lw){var _Lx=B(_G7(_Lu,_Lw));if(!B(_lx(_Lx,_Lc))){return [2];}else{return new F(function(){return A(_Lg,[new T(function(){var _Ly=B(_jt(_Lx));if(_Ly>>>0>1114111){return B(_v7(_Ly));}else{return _Ly;}})]);});}};return [1,B(_EE(_Lt,_Lv))];},_Lz=new T(function(){var _LA=new T(function(){return B(A(_Lg,[_Km]));}),_LB=new T(function(){return B(A(_Lg,[_Kg]));}),_LC=new T(function(){return B(A(_Lg,[_Ka]));}),_LD=new T(function(){return B(A(_Lg,[_K4]));}),_LE=new T(function(){return B(A(_Lg,[_JY]));}),_LF=new T(function(){return B(A(_Lg,[_JS]));}),_LG=new T(function(){return B(A(_Lg,[_JM]));}),_LH=new T(function(){return B(A(_Lg,[_JG]));}),_LI=new T(function(){return B(A(_Lg,[_JA]));}),_LJ=new T(function(){return B(A(_Lg,[_Ju]));}),_LK=new T(function(){return B(A(_Lg,[_Jo]));}),_LL=new T(function(){return B(A(_Lg,[_Ji]));}),_LM=new T(function(){return B(A(_Lg,[_Jc]));}),_LN=new T(function(){return B(A(_Lg,[_J6]));}),_LO=new T(function(){return B(A(_Lg,[_J0]));}),_LP=new T(function(){return B(A(_Lg,[_IU]));}),_LQ=new T(function(){return B(A(_Lg,[_IO]));}),_LR=new T(function(){return B(A(_Lg,[_Hk]));}),_LS=new T(function(){return B(A(_Lg,[_I2]));}),_LT=new T(function(){return B(A(_Lg,[_HW]));}),_LU=new T(function(){return B(A(_Lg,[_HQ]));}),_LV=new T(function(){return B(A(_Lg,[_HK]));}),_LW=new T(function(){return B(A(_Lg,[_HE]));}),_LX=new T(function(){return B(A(_Lg,[_Hq]));}),_LY=new T(function(){return B(A(_Lg,[_Hy]));}),_LZ=function(_M0){switch(E(_M0)){case 64:return E(_LY);case 65:return E(_LX);case 66:return E(_LW);case 67:return E(_LV);case 68:return E(_LU);case 69:return E(_LT);case 70:return E(_LS);case 71:return E(_Lh);case 72:return E(_Li);case 73:return E(_Lj);case 74:return E(_Lk);case 75:return E(_Ll);case 76:return E(_Lm);case 77:return E(_Ln);case 78:return E(_LR);case 79:return E(_LQ);case 80:return E(_LP);case 81:return E(_LO);case 82:return E(_LN);case 83:return E(_LM);case 84:return E(_LL);case 85:return E(_LK);case 86:return E(_LJ);case 87:return E(_LI);case 88:return E(_LH);case 89:return E(_LG);case 90:return E(_LF);case 91:return E(_LE);case 92:return E(_LD);case 93:return E(_LC);case 94:return E(_LB);case 95:return E(_LA);default:return [2];}};return B(_CS([0,function(_M1){return (E(_M1)==94)?[0,_LZ]:[2];}],new T(function(){return B(A(_La,[_Lg]));})));});return B(_CS([1,B(_DX(_GT,_GV,_Ls))],_Lz));});return new F(function(){return _CS([0,function(_M2){switch(E(_M2)){case 34:return E(_Lq);case 39:return E(_Lp);case 92:return E(_Lo);case 97:return E(_Lh);case 98:return E(_Li);case 102:return E(_Lm);case 110:return E(_Lk);case 114:return E(_Ln);case 116:return E(_Lj);case 118:return E(_Ll);default:return [2];}}],_Lr);});},_M3=function(_M4){return new F(function(){return A(_M4,[_a]);});},_M5=function(_M6){var _M7=E(_M6);if(!_M7[0]){return E(_M3);}else{var _M8=E(_M7[1]),_M9=_M8>>>0,_Ma=new T(function(){return B(_M5(_M7[2]));});if(_M9>887){var _Mb=u_iswspace(_M8);if(!E(_Mb)){return E(_M3);}else{var _Mc=function(_Md){var _Me=new T(function(){return B(A(_Ma,[_Md]));});return [0,function(_Mf){return E(_Me);}];};return E(_Mc);}}else{var _Mg=E(_M9);if(_Mg==32){var _Mh=function(_Mi){var _Mj=new T(function(){return B(A(_Ma,[_Mi]));});return [0,function(_Mk){return E(_Mj);}];};return E(_Mh);}else{if(_Mg-9>>>0>4){if(E(_Mg)==160){var _Ml=function(_Mm){var _Mn=new T(function(){return B(A(_Ma,[_Mm]));});return [0,function(_Mo){return E(_Mn);}];};return E(_Ml);}else{return E(_M3);}}else{var _Mp=function(_Mq){var _Mr=new T(function(){return B(A(_Ma,[_Mq]));});return [0,function(_Ms){return E(_Mr);}];};return E(_Mp);}}}}},_Mt=function(_Mu){var _Mv=new T(function(){return B(_Mt(_Mu));}),_Mw=function(_Mx){return (E(_Mx)==92)?E(_Mv):[2];},_My=function(_Mz){return [0,_Mw];},_MA=[1,function(_MB){return new F(function(){return A(_M5,[_MB,_My]);});}],_MC=new T(function(){return B(_Lf(function(_MD){return new F(function(){return A(_Mu,[[0,_MD,_v6]]);});}));}),_ME=function(_MF){var _MG=E(_MF);if(_MG==38){return E(_Mv);}else{var _MH=_MG>>>0;if(_MH>887){var _MI=u_iswspace(_MG);return (E(_MI)==0)?[2]:E(_MA);}else{var _MJ=E(_MH);return (_MJ==32)?E(_MA):(_MJ-9>>>0>4)?(E(_MJ)==160)?E(_MA):[2]:E(_MA);}}};return new F(function(){return _CS([0,function(_MK){return (E(_MK)==92)?[0,_ME]:[2];}],[0,function(_ML){var _MM=E(_ML);if(E(_MM)==92){return E(_MC);}else{return new F(function(){return A(_Mu,[[0,_MM,_v5]]);});}}]);});},_MN=function(_MO,_MP){var _MQ=new T(function(){return B(A(_MP,[[1,new T(function(){return B(A(_MO,[_3n]));})]]));}),_MR=function(_MS){var _MT=E(_MS),_MU=E(_MT[1]);if(E(_MU)==34){if(!E(_MT[2])){return E(_MQ);}else{return new F(function(){return _MN(function(_MV){return new F(function(){return A(_MO,[[1,_MU,_MV]]);});},_MP);});}}else{return new F(function(){return _MN(function(_MW){return new F(function(){return A(_MO,[[1,_MU,_MW]]);});},_MP);});}};return new F(function(){return _Mt(_MR);});},_MX=new T(function(){return B(unCStr("_\'"));}),_MY=function(_MZ){var _N0=u_iswalnum(_MZ);if(!E(_N0)){return new F(function(){return _GG(_Dt,_MZ,_MX);});}else{return true;}},_N1=function(_N2){return new F(function(){return _MY(E(_N2));});},_N3=new T(function(){return B(unCStr(",;()[]{}`"));}),_N4=new T(function(){return B(unCStr("=>"));}),_N5=[1,_N4,_3n],_N6=new T(function(){return B(unCStr("~"));}),_N7=[1,_N6,_N5],_N8=new T(function(){return B(unCStr("@"));}),_N9=[1,_N8,_N7],_Na=new T(function(){return B(unCStr("->"));}),_Nb=[1,_Na,_N9],_Nc=new T(function(){return B(unCStr("<-"));}),_Nd=[1,_Nc,_Nb],_Ne=new T(function(){return B(unCStr("|"));}),_Nf=[1,_Ne,_Nd],_Ng=new T(function(){return B(unCStr("\\"));}),_Nh=[1,_Ng,_Nf],_Ni=new T(function(){return B(unCStr("="));}),_Nj=[1,_Ni,_Nh],_Nk=new T(function(){return B(unCStr("::"));}),_Nl=[1,_Nk,_Nj],_Nm=new T(function(){return B(unCStr(".."));}),_Nn=[1,_Nm,_Nl],_No=function(_Np){var _Nq=new T(function(){return B(A(_Np,[_EB]));}),_Nr=new T(function(){var _Ns=new T(function(){var _Nt=function(_Nu){var _Nv=new T(function(){return B(A(_Np,[[0,_Nu]]));});return [0,function(_Nw){return (E(_Nw)==39)?E(_Nv):[2];}];};return B(_Lf(_Nt));}),_Nx=function(_Ny){var _Nz=E(_Ny);switch(E(_Nz)){case 39:return [2];case 92:return E(_Ns);default:var _NA=new T(function(){return B(A(_Np,[[0,_Nz]]));});return [0,function(_NB){return (E(_NB)==39)?E(_NA):[2];}];}},_NC=new T(function(){var _ND=new T(function(){return B(_MN(_Q,_Np));}),_NE=new T(function(){var _NF=new T(function(){var _NG=new T(function(){var _NH=function(_NI){var _NJ=E(_NI),_NK=u_iswalpha(_NJ);return (E(_NK)==0)?(E(_NJ)==95)?[1,B(_En(_N1,function(_NL){return new F(function(){return A(_Np,[[3,[1,_NJ,_NL]]]);});}))]:[2]:[1,B(_En(_N1,function(_NM){return new F(function(){return A(_Np,[[3,[1,_NJ,_NM]]]);});}))];};return B(_CS([0,_NH],new T(function(){return [1,B(_DX(_Fz,_GE,_Np))];})));}),_NN=function(_NO){return (!B(_GG(_Dt,_NO,_GL)))?[2]:[1,B(_En(_GM,function(_NP){var _NQ=[1,_NO,_NP];if(!B(_GG(_DC,_NQ,_Nn))){return new F(function(){return A(_Np,[[4,_NQ]]);});}else{return new F(function(){return A(_Np,[[2,_NQ]]);});}}))];};return B(_CS([0,_NN],_NG));});return B(_CS([0,function(_NR){if(!B(_GG(_Dt,_NR,_N3))){return [2];}else{return new F(function(){return A(_Np,[[2,[1,_NR,_3n]]]);});}}],_NF));});return B(_CS([0,function(_NS){return (E(_NS)==34)?E(_ND):[2];}],_NE));});return B(_CS([0,function(_NT){return (E(_NT)==39)?[0,_Nx]:[2];}],_NC));});return new F(function(){return _CS([1,function(_NU){return (E(_NU)[0]==0)?E(_Nq):[2];}],_Nr);});},_NV=0,_NW=function(_NX,_NY){var _NZ=new T(function(){var _O0=new T(function(){var _O1=function(_O2){var _O3=new T(function(){var _O4=new T(function(){return B(A(_NY,[_O2]));});return B(_No(function(_O5){var _O6=E(_O5);return (_O6[0]==2)?(!B(_26(_O6[1],_Dm)))?[2]:E(_O4):[2];}));}),_O7=function(_O8){return E(_O3);};return [1,function(_O9){return new F(function(){return A(_M5,[_O9,_O7]);});}];};return B(A(_NX,[_NV,_O1]));});return B(_No(function(_Oa){var _Ob=E(_Oa);return (_Ob[0]==2)?(!B(_26(_Ob[1],_Dl)))?[2]:E(_O0):[2];}));}),_Oc=function(_Od){return E(_NZ);};return function(_Oe){return new F(function(){return A(_M5,[_Oe,_Oc]);});};},_Of=function(_Og,_Oh){var _Oi=function(_Oj){var _Ok=new T(function(){return B(A(_Og,[_Oj]));}),_Ol=function(_Om){return new F(function(){return _CS(B(A(_Ok,[_Om])),new T(function(){return [1,B(_NW(_Oi,_Om))];}));});};return E(_Ol);},_On=new T(function(){return B(A(_Og,[_Oh]));}),_Oo=function(_Op){return new F(function(){return _CS(B(A(_On,[_Op])),new T(function(){return [1,B(_NW(_Oi,_Op))];}));});};return E(_Oo);},_Oq=function(_Or,_Os){var _Ot=function(_Ou,_Ov){var _Ow=function(_Ox){return new F(function(){return A(_Ov,[new T(function(){return  -E(_Ox);})]);});},_Oy=new T(function(){return B(_No(function(_Oz){return new F(function(){return A(_Or,[_Oz,_Ou,_Ow]);});}));}),_OA=function(_OB){return E(_Oy);},_OC=function(_OD){return new F(function(){return A(_M5,[_OD,_OA]);});},_OE=new T(function(){return B(_No(function(_OF){var _OG=E(_OF);if(_OG[0]==4){var _OH=E(_OG[1]);if(!_OH[0]){return new F(function(){return A(_Or,[_OG,_Ou,_Ov]);});}else{if(E(_OH[1])==45){if(!E(_OH[2])[0]){return [1,_OC];}else{return new F(function(){return A(_Or,[_OG,_Ou,_Ov]);});}}else{return new F(function(){return A(_Or,[_OG,_Ou,_Ov]);});}}}else{return new F(function(){return A(_Or,[_OG,_Ou,_Ov]);});}}));}),_OI=function(_OJ){return E(_OE);};return [1,function(_OK){return new F(function(){return A(_M5,[_OK,_OI]);});}];};return new F(function(){return _Of(_Ot,_Os);});},_OL=function(_OM){var _ON=E(_OM);if(!_ON[0]){var _OO=_ON[2];return [1,new T(function(){return B(_FR(new T(function(){return B(_bO(E(_ON[1])));}),new T(function(){return B(_bb(_OO,0));},1),B(_1A(_FH,_OO))));})];}else{return (E(_ON[2])[0]==0)?(E(_ON[3])[0]==0)?[1,new T(function(){return B(_G7(_FG,_ON[1]));})]:[0]:[0];}},_OP=function(_OQ,_OR){return [2];},_OS=function(_OT){var _OU=E(_OT);if(_OU[0]==5){var _OV=B(_OL(_OU[1]));if(!_OV[0]){return E(_OP);}else{var _OW=new T(function(){return B(_jt(_OV[1]));});return function(_OX,_OY){return new F(function(){return A(_OY,[_OW]);});};}}else{return E(_OP);}},_OZ=function(_P0){var _P1=function(_P2){return [3,_P0,_DO];};return [1,function(_P3){return new F(function(){return A(_M5,[_P3,_P1]);});}];},_P4=new T(function(){return B(A(_Oq,[_OS,_NV,_OZ]));}),_P5=100,_P6=[0,_6C,_6C,_6C,_6C,_v5,_3n,_P5],_P7=function(_P8){while(1){var _P9=B((function(_Pa){var _Pb=E(_Pa);if(!_Pb[0]){return [0];}else{var _Pc=_Pb[2],_Pd=E(_Pb[1]);if(!E(_Pd[2])[0]){return [1,_Pd[1],new T(function(){return B(_P7(_Pc));})];}else{_P8=_Pc;return null;}}})(_P8));if(_P9!=null){return _P9;}}},_Pe=function(_Pf){var _Pg=E(_Pf);if(!_Pg[0]){return E(_CC);}else{var _Ph=new T(function(){var _Pi=B(_P7(B(_CI(_P4,new T(function(){return B(A(E(_Pg[1])[2],[_P6,_3n]));})))));if(!_Pi[0]){return E(_CE);}else{if(!E(_Pi[2])[0]){return E(_Pi[1]);}else{return E(_CG);}}});return [0,_Pg[2],_Ph];}},_Pj=function(_Pk){return (E(_Pk)-48|0)>>>0<=9;},_Pl=0,_Pm=[1,_Pl],_Pn=0,_Po=0,_Pp=[1,_Po],_Pq=1,_Pr=[1,_Pq],_Ps=new T(function(){var _Pt=B(_kD(_Pj,_3n)),_Pu=_Pt[2],_Pv=E(_Pt[1]);if(!_Pv[0]){return [0,_Pn,_Pu];}else{return [0,new T(function(){var _Pw=B(_P7(B(_CI(_P4,_Pv))));if(!_Pw[0]){return E(_CE);}else{if(!E(_Pw[2])[0]){return E(_Pw[1]);}else{return E(_CG);}}}),_Pu];}}),_Px=new T(function(){return E(E(_Ps)[1]);}),_Py=[1,_Px],_Pz=new T(function(){return E(E(_Ps)[2]);}),_PA=1,_PB=[1,_PA],_PC=function(_PD,_PE,_PF,_PG,_PH,_PI){while(1){var _PJ=B((function(_PK,_PL,_PM,_PN,_PO,_PP){var _PQ=E(_PO);if(!_PQ[0]){return E(_gB);}else{var _PR=_PQ[2],_PS=E(_PQ[1]);switch(_PS){case 32:var _PT=_PK,_PU=_PL,_PV=_PN,_PW=_PP;_PD=_PT;_PE=_PU;_PF=new T(function(){var _PX=E(_PM);if(!_PX[0]){return E(_Pr);}else{if(!E(_PX[1])){return E(_Pp);}else{return E(_Pr);}}});_PG=_PV;_PH=_PR;_PI=_PW;return null;case 35:var _PT=_PK,_PU=_PL,_PY=_PM,_PW=_PP;_PD=_PT;_PE=_PU;_PF=_PY;_PG=_v6;_PH=_PR;_PI=_PW;return null;case 42:var _PZ=new T(function(){var _Q0=B(_Pe(_PP));return [0,_Q0[1],_Q0[2]];}),_Q1=new T(function(){var _Q2=E(_PR);if(!_Q2[0]){return [0,_6C,_3n,new T(function(){return E(E(_PZ)[1]);})];}else{if(E(_Q2[1])==46){var _Q3=E(_Q2[2]);if(!_Q3[0]){return [0,_Py,_Pz,new T(function(){return E(E(_PZ)[1]);})];}else{if(E(_Q3[1])==42){var _Q4=new T(function(){var _Q5=B(_Pe(E(_PZ)[1]));return [0,_Q5[1],_Q5[2]];});return [0,[1,new T(function(){return E(E(_Q4)[2]);})],_Q3[2],new T(function(){return E(E(_Q4)[1]);})];}else{var _Q6=new T(function(){var _Q7=B(_kD(_Pj,_Q3)),_Q8=_Q7[2],_Q9=E(_Q7[1]);if(!_Q9[0]){return [0,_Pn,_Q8];}else{return [0,new T(function(){var _Qa=B(_P7(B(_CI(_P4,_Q9))));if(!_Qa[0]){return E(_CE);}else{if(!E(_Qa[2])[0]){return E(_Qa[1]);}else{return E(_CG);}}}),_Q8];}});return [0,[1,new T(function(){return E(E(_Q6)[1]);})],new T(function(){return E(E(_Q6)[2]);}),new T(function(){return E(E(_PZ)[1]);})];}}}else{return [0,_6C,_Q2,new T(function(){return E(E(_PZ)[1]);})];}}}),_Qb=new T(function(){return E(E(_Q1)[3]);}),_Qc=new T(function(){var _Qd=E(_Qb);if(!_Qd[0]){return E(_CC);}else{return B(A(E(_Qd[1])[1],[new T(function(){return E(E(_Q1)[2]);})]));}}),_Qe=new T(function(){return E(E(_PZ)[2]);});return [0,[0,[1,new T(function(){return B(_s8(_Qe));})],new T(function(){return E(E(_Q1)[1]);}),new T(function(){if(E(_Qe)>=0){if(!E(_PK)){if(!E(_PL)){return [0];}else{return E(_PB);}}else{return E(_Pm);}}else{return E(_Pm);}}),_PM,_PN,new T(function(){return E(E(_Qc)[1]);}),new T(function(){return E(E(_Qc)[2]);})],new T(function(){return E(E(_Qc)[3]);}),_Qb];case 43:var _PT=_PK,_PU=_PL,_PV=_PN,_PW=_PP;_PD=_PT;_PE=_PU;_PF=_Pp;_PG=_PV;_PH=_PR;_PI=_PW;return null;case 45:var _PU=_PL,_PY=_PM,_PV=_PN,_PW=_PP;_PD=_v6;_PE=_PU;_PF=_PY;_PG=_PV;_PH=_PR;_PI=_PW;return null;case 46:var _Qf=new T(function(){var _Qg=E(_PR);if(!_Qg[0]){var _Qh=B(_kD(_Pj,_3n)),_Qi=_Qh[2],_Qj=E(_Qh[1]);if(!_Qj[0]){return [0,_Pn,_Qi,_PP];}else{return [0,new T(function(){var _Qk=B(_P7(B(_CI(_P4,_Qj))));if(!_Qk[0]){return E(_CE);}else{if(!E(_Qk[2])[0]){return E(_Qk[1]);}else{return E(_CG);}}}),_Qi,_PP];}}else{if(E(_Qg[1])==42){var _Ql=new T(function(){var _Qm=B(_Pe(_PP));return [0,_Qm[1],_Qm[2]];});return [0,new T(function(){return E(E(_Ql)[2]);}),_Qg[2],new T(function(){return E(E(_Ql)[1]);})];}else{var _Qn=B(_kD(_Pj,_Qg)),_Qo=_Qn[2],_Qp=E(_Qn[1]);if(!_Qp[0]){return [0,_Pn,_Qo,_PP];}else{return [0,new T(function(){var _Qq=B(_P7(B(_CI(_P4,_Qp))));if(!_Qq[0]){return E(_CE);}else{if(!E(_Qq[2])[0]){return E(_Qq[1]);}else{return E(_CG);}}}),_Qo,_PP];}}}}),_Qr=new T(function(){return E(E(_Qf)[3]);}),_Qs=new T(function(){var _Qt=E(_Qr);if(!_Qt[0]){return E(_CC);}else{return B(A(E(_Qt[1])[1],[new T(function(){return E(E(_Qf)[2]);})]));}});return [0,[0,_6C,[1,new T(function(){return E(E(_Qf)[1]);})],new T(function(){if(!E(_PK)){if(!E(_PL)){return [0];}else{return E(_PB);}}else{return E(_Pm);}}),_PM,_PN,new T(function(){return E(E(_Qs)[1]);}),new T(function(){return E(E(_Qs)[2]);})],new T(function(){return E(E(_Qs)[3]);}),_Qr];case 48:var _PT=_PK,_PY=_PM,_PV=_PN,_PW=_PP;_PD=_PT;_PE=_v6;_PF=_PY;_PG=_PV;_PH=_PR;_PI=_PW;return null;default:if((_PS-48|0)>>>0>9){var _Qu=new T(function(){var _Qv=E(_PP);if(!_Qv[0]){return E(_CC);}else{return B(A(E(_Qv[1])[1],[_PQ]));}});return [0,[0,_6C,_6C,new T(function(){if(!E(_PK)){if(!E(_PL)){return [0];}else{return E(_PB);}}else{return E(_Pm);}}),_PM,_PN,new T(function(){return E(E(_Qu)[1]);}),new T(function(){return E(E(_Qu)[2]);})],new T(function(){return E(E(_Qu)[3]);}),_PP];}else{var _Qw=new T(function(){var _Qx=B(_kD(_Pj,_PQ)),_Qy=_Qx[2],_Qz=E(_Qx[1]);if(!_Qz[0]){return [0,_Pn,_Qy];}else{return [0,new T(function(){var _QA=B(_P7(B(_CI(_P4,_Qz))));if(!_QA[0]){return E(_CE);}else{if(!E(_QA[2])[0]){return E(_QA[1]);}else{return E(_CG);}}}),_Qy];}}),_QB=new T(function(){var _QC=E(E(_Qw)[2]);if(!_QC[0]){return [0,_6C,_3n,_PP];}else{if(E(_QC[1])==46){var _QD=E(_QC[2]);if(!_QD[0]){return [0,_Py,_Pz,_PP];}else{if(E(_QD[1])==42){var _QE=new T(function(){var _QF=B(_Pe(_PP));return [0,_QF[1],_QF[2]];});return [0,[1,new T(function(){return E(E(_QE)[2]);})],_QD[2],new T(function(){return E(E(_QE)[1]);})];}else{var _QG=new T(function(){var _QH=B(_kD(_Pj,_QD)),_QI=_QH[2],_QJ=E(_QH[1]);if(!_QJ[0]){return [0,_Pn,_QI];}else{return [0,new T(function(){var _QK=B(_P7(B(_CI(_P4,_QJ))));if(!_QK[0]){return E(_CE);}else{if(!E(_QK[2])[0]){return E(_QK[1]);}else{return E(_CG);}}}),_QI];}});return [0,[1,new T(function(){return E(E(_QG)[1]);})],new T(function(){return E(E(_QG)[2]);}),_PP];}}}else{return [0,_6C,_QC,_PP];}}}),_QL=new T(function(){return E(E(_QB)[3]);}),_QM=new T(function(){var _QN=E(_QL);if(!_QN[0]){return E(_CC);}else{return B(A(E(_QN[1])[1],[new T(function(){return E(E(_QB)[2]);})]));}}),_QO=new T(function(){return E(E(_Qw)[1]);});return [0,[0,[1,new T(function(){return B(_s8(_QO));})],new T(function(){return E(E(_QB)[1]);}),new T(function(){if(E(_QO)>=0){if(!E(_PK)){if(!E(_PL)){return [0];}else{return E(_PB);}}else{return E(_Pm);}}else{return E(_Pm);}}),_PM,_PN,new T(function(){return E(E(_QM)[1]);}),new T(function(){return E(E(_QM)[2]);})],new T(function(){return E(E(_QM)[3]);}),_QL];}}}})(_PD,_PE,_PF,_PG,_PH,_PI));if(_PJ!=null){return _PJ;}}},_QP=37,_QQ=function(_QR,_QS,_QT){var _QU=E(_QR);if(!_QU[0]){return (E(_QS)[0]==0)?E(_QT):E(_gB);}else{var _QV=_QU[2],_QW=E(_QU[1]);if(E(_QW)==37){var _QX=function(_QY){var _QZ=E(_QS);if(!_QZ[0]){return E(_CC);}else{var _R0=B(_PC(_v5,_v5,_6C,_v5,_QV,_QZ)),_R1=E(_R0[3]);if(!_R1[0]){return E(_CC);}else{return new F(function(){return A(E(_R1[1])[2],[_R0[1],new T(function(){return B(_QQ(_R0[2],_R1[2],_QY));})]);});}}},_R2=E(_QV);if(!_R2[0]){return new F(function(){return _QX(_QT);});}else{if(E(_R2[1])==37){return [1,_QP,new T(function(){return B(_QQ(_R2[2],_QS,_QT));})];}else{return new F(function(){return _QX(_QT);});}}}else{return [1,_QW,new T(function(){return B(_QQ(_QV,_QS,_QT));})];}}},_R3=function(_R4,_R5){return new F(function(){return _1A(_Cz,B(_QQ(_R4,new T(function(){return B(_cJ(_R5,_3n));},1),_3n)));});},_R6=function(_R7,_R8,_R9,_Ra,_Rb){if(_R8!=_Ra){return new F(function(){return _b3(_R7,_R8,_Ra);});}else{return new F(function(){return _b3(_R7,E(_R9),E(_Rb));});}},_Rc=new T(function(){return B(unCStr("%.3f"));}),_Rd=32,_Re=new T(function(){return B(unCStr("ccdtrans sav"));}),_Rf=new T(function(){return B(unCStr("  ccdacq"));}),_Rg=new T(function(){return B(unAppCStr("}",_gu));}),_Rh=new T(function(){return B(_16(_gu,_Rg));}),_Ri=new T(function(){return B(unCStr("\""));}),_Rj=new T(function(){return B(_83(0,1,_3n));}),_Rk=new T(function(){return B(unCStr("1"));}),_Rl=new T(function(){return B(_16(_Rk,_3n));}),_Rm=[1,_Rd,_Rl],_Rn=new T(function(){return B(_16(_Rj,_Rm));}),_Ro=[1,_Rd,_Rn],_Rp=new T(function(){var _Rq=jsShow(0);return fromJSStr(_Rq);}),_Rr=new T(function(){var _Rs=jsShow(4.0e-2);return fromJSStr(_Rs);}),_Rt=function(_Ru){return new F(function(){return _R3(_Rc,[1,[0,function(_Rv){return new F(function(){return _gC(_Ru,_Rv);});},function(_Rv){return new F(function(){return _Cv(_Ru,_Rv);});}],_3n]);});},_Rw=function(_Rx,_Ry,_Rz,_RA){if(!E(_Rx)){var _RB=new T(function(){var _RC=new T(function(){var _RD=E(E(_Rz)[1])[2],_RE=E(_Ry);if(!E(_RE[6])){return E(_RE[3])+E(_RD)*25/900;}else{return E(_RE[4])+E(_RD)*25/900;}}),_RF=new T(function(){var _RG=new T(function(){var _RH=new T(function(){var _RI=E(_Ry),_RJ=_RI[5],_RK=E(_Rz),_RL=E(_RK[1]),_RM=E(_RL[1]),_RN=E(_RK[2]),_RO=E(_RN[1]),_RP=B(_R6(E(_RI[7]),_RM,_RL[2],_RO,_RN[2])),_RQ=new T(function(){var _RR=new T(function(){var _RS=new T(function(){var _RT=new T(function(){var _RU=new T(function(){var _RV=new T(function(){var _RW=new T(function(){return E(_RJ)+12.5+(_RM*25/900-12.5)*Math.cos(E(_RA));}),_RX=new T(function(){var _RY=new T(function(){var _RZ=new T(function(){return (E(_RJ)+12.5+(_RO*25/900-12.5)*Math.cos(E(_RA))-E(_RW))/_RP;}),_S0=new T(function(){var _S1=new T(function(){var _S2=new T(function(){var _S3=new T(function(){return (_RM*25/900-12.5)*Math.sin(E(_RA));}),_S4=new T(function(){var _S5=new T(function(){var _S6=new T(function(){return ((_RO*25/900-12.5)*Math.sin(E(_RA))-E(_S3))/_RP;}),_S7=new T(function(){var _S8=new T(function(){var _S9=new T(function(){var _Sa=new T(function(){var _Sb=new T(function(){var _Sc=new T(function(){var _Sd=new T(function(){var _Se=new T(function(){return B(_16(B(unAppCStr("\"",new T(function(){return B(_16(_RK[3],_Ri));}))),_3n));});return B(_16(_Rr,[1,_Rd,_Se]));});return B(_16(B(_16(_Rf,[1,_Rd,_Sd])),_Rh));},1);return B(_16(_gu,_Sc));});return B(unAppCStr("  umv tmp2 x",_Sb));},1);return B(_16(_gu,_Sa));});return B(unAppCStr("  umv sah y",_S9));},1);return B(_16(_gu,_S8));},1);return B(_16(B(_R3(_Rc,[1,[0,function(_Rv){return new F(function(){return _gC(_S6,_Rv);});},function(_Rv){return new F(function(){return _Cv(_S6,_Rv);});}],_3n])),_S7));});return B(unAppCStr("+i*",_S5));},1);return B(_16(B(_Rt(_S3)),_S4));});return B(unAppCStr("  x = ",_S2));},1);return B(_16(_gu,_S1));},1);return B(_16(B(_R3(_Rc,[1,[0,function(_Rv){return new F(function(){return _gC(_RZ,_Rv);});},function(_Rv){return new F(function(){return _Cv(_RZ,_Rv);});}],_3n])),_S0));});return B(unAppCStr("+i*",_RY));},1);return B(_16(B(_Rt(_RW)),_RX));});return B(unAppCStr("  y = ",_RV));},1);return B(_16(_gu,_RU));});return B(unAppCStr("{",_RT));},1);return B(_16(_gu,_RS));});return B(unAppCStr(";i+=1)",_RR));},1);return B(_16(B(_83(0,_RP,_3n)),_RQ));});return B(unAppCStr("for(i=0;i<=",_RH));},1);return B(_16(_gu,_RG));},1);return B(_16(B(_R3(_Rc,[1,[0,function(_Rv){return new F(function(){return _gC(_RC,_Rv);});},function(_Rv){return new F(function(){return _Cv(_RC,_Rv);});}],_3n])),_RF));});return new F(function(){return unAppCStr("umv sav ",_RB);});}else{var _Sf=new T(function(){var _Sg=new T(function(){return E(E(_Ry)[5])+12.5+(E(E(E(_Rz)[1])[1])*25/900-12.5)*Math.cos(E(_RA));}),_Sh=new T(function(){var _Si=new T(function(){var _Sj=new T(function(){return (E(E(E(_Rz)[1])[1])*25/900-12.5)*Math.sin(E(_RA));}),_Sk=new T(function(){var _Sl=new T(function(){var _Sm=new T(function(){var _Sn=new T(function(){var _So=E(E(_Rz)[1])[2],_Sp=E(_Ry);if(!E(_Sp[6])){return E(_Sp[3])+E(_So)*25/900;}else{return E(_Sp[4])+E(_So)*25/900;}}),_Sq=new T(function(){var _Sr=new T(function(){var _Ss=E(E(_Rz)[2])[2],_St=E(_Ry);if(!E(_St[6])){return E(_St[3])+E(_Ss)*25/900;}else{return E(_St[4])+E(_Ss)*25/900;}}),_Su=new T(function(){var _Sv=E(_Rz),_Sw=E(_Sv[1]),_Sx=E(_Sv[2]),_Sy=new T(function(){var _Sz=new T(function(){var _SA=new T(function(){return B(_16(B(unAppCStr("\"",new T(function(){return B(_16(_Sv[3],_Ri));}))),_Ro));});return B(_16(_Rp,[1,_Rd,_SA]));});return B(_16(_Rr,[1,_Rd,_Sz]));});return B(_16(B(_83(0,B(_R6(E(E(_Ry)[7]),E(_Sw[1]),_Sw[2],E(_Sx[1]),_Sx[2])),_3n)),[1,_Rd,_Sy]));});return B(_16(B(_R3(_Rc,[1,[0,function(_Rv){return new F(function(){return _gC(_Sr,_Rv);});},function(_Rv){return new F(function(){return _Cv(_Sr,_Rv);});}],_3n])),[1,_Rd,_Su]));});return B(_16(B(_R3(_Rc,[1,[0,function(_Rv){return new F(function(){return _gC(_Sn,_Rv);});},function(_Rv){return new F(function(){return _Cv(_Sn,_Rv);});}],_3n])),[1,_Rd,_Sq]));});return B(_16(_Re,[1,_Rd,_Sm]));},1);return B(_16(_gu,_Sl));},1);return B(_16(B(_R3(_Rc,[1,[0,function(_Rv){return new F(function(){return _gC(_Sj,_Rv);});},function(_Rv){return new F(function(){return _Cv(_Sj,_Rv);});}],_3n])),_Sk));});return B(unAppCStr(" tmp2 ",_Si));},1);return B(_16(B(_R3(_Rc,[1,[0,function(_Rv){return new F(function(){return _gC(_Sg,_Rv);});},function(_Rv){return new F(function(){return _Cv(_Sg,_Rv);});}],_3n])),_Sh));});return new F(function(){return unAppCStr("umv sah ",_Sf);});}},_SB=function(_SC,_SD,_SE,_SF,_SG,_SH,_SI){var _SJ=[0,_gq,_SC,_SD,_SE,_SF,_SG,_SH,_SI],_SK=function(_SL){var _SM=new T(function(){var _SN=E(_SL),_SO=rintDouble(_SN*180/3.141592653589793),_SP=B(_bI(_SO)),_SQ=_SP[1],_SR=_SP[2],_SS=new T(function(){var _ST=new T(function(){var _SU=B(_1A(function(_SV){var _SW=E(_SV);if(E(E(_SW[1])[1])!=E(E(_SW[2])[1])){return new F(function(){return _Rw(_gm,_SJ,_SW,_SN);});}else{return new F(function(){return _Rw(_gn,_SJ,_SW,_SN);});}},B(_cJ(_SC,_3n))));if(!_SU[0]){return [0];}else{return B(_gr([1,_SU[1],new T(function(){return B(_gw(_gu,_SU[2]));})]));}},1);return B(_16(_gu,_ST));});if(_SR>=0){return B(_16(B(_gi(0,B(_cO(_SQ,_SR)),_3n)),_SS));}else{var _SX=hs_uncheckedIShiftRA64(B(_c0(_SQ)), -_SR);return B(_16(B(_gi(0,B(_bQ(_SX)),_3n)),_SS));}});return new F(function(){return unAppCStr("umv sar ",_SM);});},_SY=B(_1A(_SK,_SI));if(!_SY[0]){return [0];}else{return new F(function(){return _gr([1,_SY[1],new T(function(){return B(_gw(_gv,_SY[2]));})]);});}},_SZ=(function(id){return document.getElementById(id);}),_T0=function(_T1,_T2){var _T3=function(_){var _T4=E(_SZ)(E(_T2)),_T5=__eq(_T4,E(_8Y));return (E(_T5)==0)?[1,_T4]:_6C;};return new F(function(){return A(_2,[_T1,_T3]);});},_T6=new T(function(){return encodeURIComponent;}),_T7=new T(function(){return B(unCStr("data:text/plain;charset=utf-8,"));}),_T8=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:188:3-9"));}),_T9=[0,_6C,_6D,_3n,_T8,_6C,_6C],_Ta=new T(function(){return B(_6A(_T9));}),_Tb=new T(function(){return B(unCStr("href"));}),_Tc=function(_Td){return new F(function(){return toJSStr(E(_Td));});},_Te=function(_Tf,_Tg,_){var _Th=B(A(_T0,[_6K,new T(function(){return B(_Tc(_Tf));},1),_])),_Ti=E(_Th);if(!_Ti[0]){return new F(function(){return die(_Ta);});}else{var _Tj=E(_T6)(toJSStr(_Tg)),_Tk=E(_9C)(E(_Ti[1]),toJSStr(E(_Tb)),toJSStr(B(_16(_T7,new T(function(){var _Tl=String(_Tj);return fromJSStr(_Tl);},1)))));return new F(function(){return _eV(_);});}},_Tm=(function(ctx,rad){ctx.rotate(rad);}),_Tn=function(_To,_Tp,_Tq,_){var _Tr=E(_eX)(_Tq),_Ts=E(_Tm)(_Tq,E(_To)),_Tt=B(A(_Tp,[_Tq,_])),_Tu=E(_eW)(_Tq);return new F(function(){return _eV(_);});},_Tv=(function(ctx,x,y){ctx.translate(x,y);}),_Tw=function(_Tx,_Ty,_Tz,_TA,_){var _TB=E(_eX)(_TA),_TC=E(_Tv)(_TA,E(_Tx),E(_Ty)),_TD=B(A(_Tz,[_TA,_])),_TE=E(_eW)(_TA);return new F(function(){return _eV(_);});},_TF=function(_TG,_TH,_TI,_TJ,_TK,_TL,_TM,_TN){return new F(function(){return Math.atan((Math.tan(B(_nA(new T(function(){return B(_mS(_TJ,_TH));}),_TI-_TG))-1.5707963267948966)+Math.tan(B(_nA(new T(function(){return B(_mS(_TL,_TJ));}),_TK-_TI)))+Math.tan(B(_nA(new T(function(){return B(_mS(_TN,_TL));}),_TM-_TK))+1.5707963267948966)+Math.tan(B(_nA(new T(function(){return B(_mS(_TH,_TN));}),_TG-_TM))-3.141592653589793))/4);});},_TO=function(_TP){return E(_TP)/2;},_TQ=function(_TR,_TS,_TT,_){var _TU=E(_TR);return new F(function(){return _Tw(_TU[1],_TU[2],_TS,E(_TT),_);});},_TV=function(_TW,_TX){var _TY=new T(function(){var _TZ=E(_TW),_U0=E(E(_TX)[2]),_U1=E(_U0[1]),_U2=E(_U1[1]),_U3=E(_U1[2]),_U4=E(_U0[2]),_U5=E(_U4[1]),_U6=E(_U4[2]),_U7=E(_U0[3]),_U8=E(_U7[1]),_U9=E(_U7[2]),_Ua=E(_U0[4]),_Ub=E(_Ua[1]),_Uc=E(_Ua[2]);return Math.sqrt(E(_TZ[1])*E(_TZ[2])/(0.5*(_U2*_Uc+_Ub*_U9+_U8*_U3-_U2*_U9-_U8*_Uc-_Ub*_U3)+0.5*(_Ub*_U9+_U8*_U6+_U5*_Uc-_Ub*_U6-_U5*_U9-_U8*_Uc)));}),_Ud=new T(function(){var _Ue=E(_TW);return [0,new T(function(){return B(_TO(_Ue[1]));}),new T(function(){return B(_TO(_Ue[2]));})];}),_Uf=new T(function(){var _Ug=E(E(_TX)[2]),_Uh=E(_Ug[1]),_Ui=E(_Ug[2]),_Uj=E(_Ug[3]),_Uk=E(_Ug[4]);return  -B(_TF(E(_Uh[1]),_Uh[2],E(_Ui[1]),_Ui[2],E(_Uj[1]),_Uj[2],E(_Uk[1]),_Uk[2]));}),_Ul=new T(function(){var _Um=E(E(_TX)[2]),_Un=E(_Um[1]),_Uo=E(_Um[2]),_Up=E(_Um[3]),_Uq=E(_Um[4]);return [0,new T(function(){return (E(_Un[1])+E(_Uo[1])+E(_Up[1])+E(_Uq[1]))/4/(-1);}),new T(function(){return (E(_Un[2])+E(_Uo[2])+E(_Up[2])+E(_Uq[2]))/4/(-1);})];}),_Ur=function(_Us,_Ut,_){var _Uu=E(_Ud),_Uv=function(_Uw,_){var _Ux=function(_Uy,_){return new F(function(){return _Tn(_Uf,function(_Uz,_){return new F(function(){return _TQ(_Ul,_Us,_Uz,_);});},E(_Uy),_);});};return new F(function(){return _eZ(_TY,_TY,_Ux,E(_Uw),_);});};return new F(function(){return _Tw(_Uu[1],_Uu[2],_Uv,E(_Ut),_);});};return E(_Ur);},_UA=(function(ctx,x,y){ctx.moveTo(x,y);}),_UB=(function(ctx,x,y){ctx.lineTo(x,y);}),_UC=function(_UD,_UE,_){var _UF=E(_UD);if(!_UF[0]){return _a;}else{var _UG=E(_UF[1]),_UH=E(_UE),_UI=E(_UA)(_UH,E(_UG[1]),E(_UG[2])),_UJ=E(_UF[2]);if(!_UJ[0]){return _a;}else{var _UK=E(_UJ[1]),_UL=E(_UB),_UM=_UL(_UH,E(_UK[1]),E(_UK[2])),_UN=_UJ[2];while(1){var _UO=E(_UN);if(!_UO[0]){return _a;}else{var _UP=E(_UO[1]),_UQ=_UL(_UH,E(_UP[1]),E(_UP[2]));_UN=_UO[2];continue;}}}}},_UR=function(_US,_UT,_){var _UU=new T(function(){return E(E(_US)[2]);}),_UV=new T(function(){return E(E(_UU)[1]);});return new F(function(){return _UC([1,_UV,[1,new T(function(){return E(E(_UU)[2]);}),[1,new T(function(){return E(E(_UU)[3]);}),[1,new T(function(){return E(E(_UU)[4]);}),[1,_UV,_3n]]]]],_UT,_);});},_UW=(function(e){e.width = e.width;}),_UX=",",_UY="rgba(",_UZ=new T(function(){return toJSStr(_3n);}),_V0="rgb(",_V1=")",_V2=[1,_V1,_3n],_V3=function(_V4){var _V5=E(_V4);if(!_V5[0]){var _V6=jsCat([1,_V0,[1,new T(function(){return String(_V5[1]);}),[1,_UX,[1,new T(function(){return String(_V5[2]);}),[1,_UX,[1,new T(function(){return String(_V5[3]);}),_V2]]]]]],E(_UZ));return E(_V6);}else{var _V7=jsCat([1,_UY,[1,new T(function(){return String(_V5[1]);}),[1,_UX,[1,new T(function(){return String(_V5[2]);}),[1,_UX,[1,new T(function(){return String(_V5[3]);}),[1,_UX,[1,new T(function(){return String(_V5[4]);}),_V2]]]]]]]],E(_UZ));return E(_V7);}},_V8="strokeStyle",_V9="fillStyle",_Va=(function(e,p){return e[p].toString();}),_Vb=function(_Vc,_Vd){var _Ve=new T(function(){return B(_V3(_Vc));});return function(_Vf,_){var _Vg=E(_Vf),_Vh=E(_V9),_Vi=E(_Va),_Vj=_Vi(_Vg,_Vh),_Vk=E(_V8),_Vl=_Vi(_Vg,_Vk),_Vm=E(_Ve),_Vn=E(_1),_Vo=_Vn(_Vg,_Vh,_Vm),_Vp=_Vn(_Vg,_Vk,_Vm),_Vq=B(A(_Vd,[_Vg,_])),_Vr=String(_Vj),_Vs=_Vn(_Vg,_Vh,_Vr),_Vt=String(_Vl),_Vu=_Vn(_Vg,_Vk,_Vt);return new F(function(){return _eV(_);});};},_Vv=function(_Vw,_Vx,_Vy){var _Vz=E(_Vy);if(!_Vz[0]){return [0];}else{var _VA=_Vz[1],_VB=_Vz[2];return (!B(A(_Vw,[_Vx,_VA])))?[1,_VA,new T(function(){return B(_Vv(_Vw,_Vx,_VB));})]:E(_VB);}},_VC="lineWidth",_VD=function(_VE,_VF){var _VG=new T(function(){return String(E(_VE));});return function(_VH,_){var _VI=E(_VH),_VJ=E(_VC),_VK=E(_Va)(_VI,_VJ),_VL=E(_1),_VM=_VL(_VI,_VJ,E(_VG)),_VN=B(A(_VF,[_VI,_])),_VO=String(_VK),_VP=_VL(_VI,_VJ,_VO);return new F(function(){return _eV(_);});};},_VQ=new T(function(){return B(unCStr("saveLink"));}),_VR=new T(function(){return B(unCStr("exportLink"));}),_VS=[0,255,0,255],_VT=1,_VU=0.2,_VV=900,_VW=[0,_VV,_VV],_VX=new T(function(){return B(unCStr("btn btn-primary"));}),_VY=new T(function(){return B(unCStr("class"));}),_VZ=new T(function(){return B(unCStr("btn btn-primary disabled"));}),_W0="exportLink",_W1=new T(function(){return B(_T0(_6K,_W0));}),_W2="scans",_W3=new T(function(){return B(_T0(_6K,_W2));}),_W4=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:166:3-8"));}),_W5=[0,_6C,_6D,_3n,_W4,_6C,_6C],_W6=new T(function(){return B(_6A(_W5));}),_W7=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:150:3-10"));}),_W8=[0,_6C,_6D,_3n,_W7,_6C,_6C],_W9=new T(function(){return B(_6A(_W8));}),_Wa=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:149:3-11"));}),_Wb=[0,_6C,_6D,_3n,_Wa,_6C,_6C],_Wc=new T(function(){return B(_6A(_Wb));}),_Wd="aligned",_We=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:148:3-11"));}),_Wf=[0,_6C,_6D,_3n,_We,_6C,_6C],_Wg=new T(function(){return B(_6A(_Wf));}),_Wh="original",_Wi=function(_Wj,_Wk,_){while(1){var _Wl=E(_Wj);if(!_Wl[0]){return _a;}else{var _Wm=E(_Wl[1]),_Wn=B(_UC([1,_Wm[1],[1,_Wm[2],_3n]],_Wk,_));_Wj=_Wl[2];continue;}}},_Wo=[0,255,0,255],_Wp=1,_Wq=function(_Wr){var _Ws=new T(function(){var _Wt=function(_Ci,_Wu){return new F(function(){return _Wi(E(_Wr)[2],_Ci,_Wu);});};return B(_Vb(_Wo,function(_Wv,_){return new F(function(){return _fa(_Wt,E(_Wv),_);});}));});return new F(function(){return _VD(_Wp,_Ws);});},_Ww=function(_Wx){while(1){var _Wy=E(_Wx);if(!_Wy[0]){return false;}else{var _Wz=E(_Wy[1]);if(!_Wz[0]){return true;}else{if(!B(_GG(_Dt,_Rd,_Wz))){_Wx=_Wy[2];continue;}else{return true;}}}}},_WA=function(_WB){return E(E(_WB)[3]);},_WC=function(_WD){return new F(function(){return fromJSStr(E(_WD));});},_WE=function(_WF,_WG,_WH,_WI){var _WJ=new T(function(){var _WK=function(_){var _WL=E(_Va)(B(A(_9A,[_WF,_WH])),E(_WI));return new T(function(){return String(_WL);});};return E(_WK);});return new F(function(){return A(_2,[_WG,_WJ]);});},_WM=function(_WN,_WO,_WP,_WQ){var _WR=B(_9r(_WO)),_WS=new T(function(){return B(_9x(_WR));}),_WT=function(_WU){return new F(function(){return A(_WS,[new T(function(){return B(_WC(_WU));})]);});},_WV=new T(function(){return B(_WE(_WN,_WO,_WP,new T(function(){return toJSStr(E(_WQ));},1)));});return new F(function(){return A(_9v,[_WR,_WV,_WT]);});},_WW=new T(function(){return B(unCStr("value"));}),_WX=function(_WY,_WZ,_X0){var _X1=E(_X0);if(!_X1[0]){return [0];}else{var _X2=_X1[1],_X3=_X1[2];return (!B(A(_WY,[_X2])))?[1,_X2,new T(function(){return B(_WX(_WY,_WZ,_X3));})]:[1,new T(function(){return B(A(_WZ,[_X2]));}),new T(function(){return B(_WX(_WY,_WZ,_X3));})];}},_X4=function(_X5,_X6,_X7,_X8,_){var _X9=B(A(_WM,[_S,_6K,_X7,_WW,_])),_Xa=_X9,_Xb=E(_X6),_Xc=rMV(_Xb),_Xd=E(_Xc),_Xe=new T(function(){return B(_WX(function(_Xf){return new F(function(){return _6X(_Xf,_X8);});},function(_Xg){var _Xh=E(_Xg);return [0,_Xh[1],_Xh[2],_Xa];},_Xd[2]));}),_=wMV(_Xb,[0,_Xd[1],_Xe,_Xd[3],_Xd[4],_Xd[5],_Xd[6],_Xd[7],_Xd[8]]);return new F(function(){return A(_X5,[_]);});},_Xi=function(_Xj,_Xk,_Xl,_){var _Xm=rMV(_Xk),_Xn=_Xm,_Xo=E(_Xj),_Xp=rMV(_Xo),_Xq=_Xp,_Xr=B(A(_T0,[_6K,_Wh,_])),_Xs=E(_Xr);if(!_Xs[0]){return new F(function(){return die(_Wg);});}else{var _Xt=E(_Xs[1]),_Xu=E(_N),_Xv=_Xu(_Xt);if(!_Xv){return new F(function(){return die(_Wg);});}else{var _Xw=E(_M),_Xx=_Xw(_Xt),_Xy=_Xx,_Xz=B(A(_T0,[_6K,_Wd,_])),_XA=function(_,_XB){var _XC=E(_XB);if(!_XC[0]){return new F(function(){return die(_Wc);});}else{var _XD=B(A(_W3,[_])),_XE=E(_XD);if(!_XE[0]){return new F(function(){return die(_W9);});}else{var _XF=B(A(_W1,[_])),_XG=E(_XF);if(!_XG[0]){return new F(function(){return die(_W6);});}else{var _XH=_XG[1],_XI=E(_Xq),_XJ=_XI[2],_XK=_XI[8],_XL=function(_){var _XM=function(_XN,_){var _XO=rMV(_Xo),_XP=E(_XO),_=wMV(_Xo,[0,_XP[1],new T(function(){return B(_Vv(_6X,_XN,_XP[2]));}),_XP[3],_XP[4],_XP[5],_XP[6],_XP[7],_XP[8]]);return new F(function(){return _Xi(_Xo,_Xk,_Xl,_);});},_XQ=function(_){return new F(function(){return _Xi(_Xo,_Xk,_Xl,_);});},_XR=B(_cS(function(_XS,_XT,_){return new F(function(){return _X4(_XQ,_Xo,_XS,_XT,_);});},_XM,_XI,E(_XE[1]),_)),_XU=E(_Xl),_XV=rMV(_XU),_XW=_XV,_XX=E(_XC[1]),_XY=_XX[1],_XZ=E(_UW),_Y0=_XZ(_XX[2]),_Y1=function(_Y2,_){return new F(function(){return _fh(E(_XW),0,0,E(_Y2),_);});},_Y3=B(A(_TV,[_VW,_Xn,function(_Y4,_){return new F(function(){return _eZ(_VU,_VU,_Y1,E(_Y4),_);});},_XY,_])),_Y5=B(A(_Wq,[_XI,_XY,_])),_Y6=rMV(_XU),_Y7=_Y6,_Y8=_XZ(_Xt),_Y9=B(_eZ(_VU,_VU,function(_Ya,_){return new F(function(){return _fh(E(_Y7),0,0,E(_Ya),_);});},_Xy,_)),_Yb=new T(function(){var _Yc=function(_XT,_){return new F(function(){return _UR(_Xn,_XT,_);});};return B(_Vb(_VS,function(_Yd,_){return new F(function(){return _fa(_Yc,E(_Yd),_);});}));}),_Ye=B(A(_VD,[_VT,_Yb,_Xy,_])),_Yf=B(_Te(_VR,new T(function(){return B(_SB(_XJ,_XI[3],_XI[4],_XI[5],_XI[6],_XI[7],_XK));},1),_)),_Yg=new T(function(){return fromJSStr(B(_fZ([4,E(B(_7L(_77,[1,new T(function(){return [4,E(B(_7p(_Xn)))];}),[1,new T(function(){return [4,E(B(_7Q(_XI)))];}),_3n]])))])));},1);return new F(function(){return _Te(_VQ,_Yg,_);});},_Yh=function(_Yi){var _Yj=E(_9C)(E(_XH),toJSStr(E(_VY)),toJSStr(E(_VZ)));return new F(function(){return _XL(_);});},_Yk=E(_XJ);if(!_Yk[0]){return new F(function(){return _Yh(_);});}else{if(!B(_Ww(B(_1A(_WA,_Yk))))){if(!E(_XK)[0]){return new F(function(){return _Yh(_);});}else{var _Yl=E(_9C)(E(_XH),toJSStr(E(_VY)),toJSStr(E(_VX)));return new F(function(){return _XL(_);});}}else{return new F(function(){return _Yh(_);});}}}}}},_Ym=E(_Xz);if(!_Ym[0]){return new F(function(){return _XA(_,_6C);});}else{var _Yn=E(_Ym[1]),_Yo=_Xu(_Yn);if(!_Yo){return new F(function(){return _XA(_,_6C);});}else{var _Yp=_Xw(_Yn);return new F(function(){return _XA(_,[1,[0,_Yp,_Yn]]);});}}}}},_Yq=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:102:3-9"));}),_Yr=[0,_6C,_6D,_3n,_Yq,_6C,_6C],_Ys=new T(function(){return B(_6A(_Yr));}),_Yt=function(_){return new F(function(){return die(_Ys);});},_Yu=2,_Yv=function(_Yw){return E(_Yw)[2];},_Yx=function(_){return _6C;},_Yy=function(_Yz,_){return new F(function(){return _Yx(_);});},_YA=[0,_Yv,_Yy],_YB=function(_YC,_YD){while(1){var _YE=E(_YC);if(!_YE[0]){return E(_YD);}else{var _YF=_YE[2],_YG=E(_YE[1]);if(_YD>_YG){_YC=_YF;_YD=_YG;continue;}else{_YC=_YF;continue;}}}},_YH=function(_YI,_YJ,_YK){var _YL=E(_YI);if(_YK>_YL){return new F(function(){return _YB(_YJ,_YL);});}else{return new F(function(){return _YB(_YJ,_YK);});}},_YM=2,_YN=4,_YO=3,_YP=function(_YQ,_YR){var _YS=function(_YT,_YU){while(1){var _YV=B((function(_YW,_YX){var _YY=E(_YW);if(!_YY[0]){return [0];}else{var _YZ=_YY[2];if(!B(A(_YQ,[_YY[1]]))){var _Z0=_YX+1|0;_YT=_YZ;_YU=_Z0;return null;}else{return [1,_YX,new T(function(){return B(_YS(_YZ,_YX+1|0));})];}}})(_YT,_YU));if(_YV!=null){return _YV;}}},_Z1=B(_YS(_YR,0));return (_Z1[0]==0)?[0]:[1,_Z1[1]];},_Z2=function(_Z3){return E(_Z3);},_Z4=function(_Z5,_Z6,_Z7,_){var _Z8=function(_Z9,_){var _Za=E(_Z5),_Zb=rMV(_Za),_Zc=E(E(_Zb)[2]),_Zd=new T(function(){var _Ze=new T(function(){var _Zf=E(E(_Z9)[1]);return [0,new T(function(){return B(_Z2(_Zf[1]));}),new T(function(){return B(_Z2(_Zf[2]));})];}),_Zg=new T(function(){var _Zh=E(_Ze),_Zi=E(_Zc[1]);return Math.pow(E(_Zh[1])-E(_Zi[1]),2)+Math.pow(E(_Zh[2])-E(_Zi[2]),2);}),_Zj=new T(function(){var _Zk=E(_Ze),_Zl=E(_Zc[2]);return Math.pow(E(_Zk[1])-E(_Zl[1]),2)+Math.pow(E(_Zk[2])-E(_Zl[2]),2);}),_Zm=[1,new T(function(){var _Zn=E(_Ze),_Zo=E(_Zc[3]);return Math.pow(E(_Zn[1])-E(_Zo[1]),2)+Math.pow(E(_Zn[2])-E(_Zo[2]),2);}),[1,new T(function(){var _Zp=E(_Ze),_Zq=E(_Zc[4]);return Math.pow(E(_Zp[1])-E(_Zq[1]),2)+Math.pow(E(_Zp[2])-E(_Zq[2]),2);}),_3n]],_Zr=new T(function(){return B(_YH(_Zj,_Zm,E(_Zg)));}),_Zs=B(_YP(function(_Zt){return E(_Zr)==E(_Zt);},[1,_Zg,[1,_Zj,_Zm]]));if(!_Zs[0]){return 3;}else{switch(E(_Zs[1])){case 0:return 0;break;case 1:return 2;break;case 3:return 1;break;default:return 3;}}}),_=wMV(_Za,[0,[1,_Zd],_Zc]);return new F(function(){return A(_Z7,[_]);});},_Zu=B(A(_ch,[_6L,_YA,_9p,_Z6,_YM,_Z8,_])),_Zv=B(A(_ch,[_6L,_YA,_9p,_Z6,_YO,function(_Zw,_){var _Zx=E(_Z5),_Zy=rMV(_Zx),_=wMV(_Zx,[0,_1Q,E(_Zy)[2]]);return new F(function(){return A(_Z7,[_]);});},_])),_Zz=function(_ZA,_){var _ZB=E(_Z5),_ZC=rMV(_ZB),_ZD=E(_ZC),_ZE=_ZD[2],_ZF=E(_ZD[1]);if(!_ZF[0]){var _ZG=E(_ZD);}else{var _ZH=new T(function(){var _ZI=E(E(_ZA)[1]);return [0,new T(function(){return B(_Z2(_ZI[1]));}),new T(function(){return B(_Z2(_ZI[2]));})];});switch(E(_ZF[1])){case 0:var _ZJ=E(_ZE),_ZK=[0,_ZF,[0,_ZH,_ZJ[2],_ZJ[3],_ZJ[4]]];break;case 1:var _ZL=E(_ZE),_ZK=[0,_ZF,[0,_ZL[1],_ZL[2],_ZL[3],_ZH]];break;case 2:var _ZM=E(_ZE),_ZK=[0,_ZF,[0,_ZM[1],_ZH,_ZM[3],_ZM[4]]];break;default:var _ZN=E(_ZE),_ZK=[0,_ZF,[0,_ZN[1],_ZN[2],_ZH,_ZN[4]]];}var _ZG=_ZK;}var _=wMV(_ZB,_ZG);return new F(function(){return A(_Z7,[_]);});},_ZO=B(A(_ch,[_6L,_YA,_9p,_Z6,_YN,_Zz,_]));return _a;},_ZP=function(_ZQ,_ZR,_ZS,_ZT,_ZU,_ZV,_ZW,_ZX,_ZY){if(!E(_ZR)){return [0,_2W,_ZS,_ZT,_ZU,_ZV,_ZW,_ZX,_ZY];}else{var _ZZ=E(_ZS);if(!_ZZ[0]){return [0,_2U,_3n,_ZT,_ZU,_ZV,_ZW,_ZX,_ZY];}else{var _100=new T(function(){return E(E(_ZZ[1])[1]);});return [0,_2U,[1,[0,_100,new T(function(){var _101=E(_100),_102=_101[1],_103=E(E(_ZQ)[1]),_104=_103[1],_105=E(_103[2]),_106=E(_101[2]),_107=_105-_106;if(!_107){var _108=E(_104),_109=E(_102),_10a=_108-_109;if(!_10a){return [0,_108,_106];}else{if(_10a<=0){if(0<= -_10a){return [0,_108,_106];}else{return [0,_109,_105];}}else{if(0<=_10a){return [0,_108,_106];}else{return [0,_109,_105];}}}}else{if(_107<=0){var _10b=E(_104),_10c=E(_102),_10d=_10b-_10c;if(!_10d){if( -_107<=0){return [0,_10b,_106];}else{return [0,_10c,_105];}}else{if(_10d<=0){if( -_107<= -_10d){return [0,_10b,_106];}else{return [0,_10c,_105];}}else{if( -_107<=_10d){return [0,_10b,_106];}else{return [0,_10c,_105];}}}}else{var _10e=E(_104),_10f=E(_102),_10g=_10e-_10f;if(!_10g){return [0,_10f,_105];}else{if(_10g<=0){if(_107<= -_10g){return [0,_10e,_106];}else{return [0,_10f,_105];}}else{if(_107<=_10g){return [0,_10e,_106];}else{return [0,_10f,_105];}}}}}}),_3n],_ZZ[2]],_ZT,_ZU,_ZV,_ZW,_ZX,_ZY];}}},_10h=function(_10i,_10j,_10k,_){var _10l=function(_10m,_){var _10n=E(_10i),_10o=rMV(_10n),_10p=E(_10o),_10q=new T(function(){var _10r=E(E(_10m)[1]);return [0,new T(function(){return B(_Z2(_10r[1]));}),new T(function(){return B(_Z2(_10r[2]));})];}),_=wMV(_10n,[0,_2U,[1,[0,_10q,_10q,_3n],_10p[2]],_10p[3],_10p[4],_10p[5],_10p[6],_10p[7],_10p[8]]);return new F(function(){return A(_10k,[_]);});},_10s=B(A(_ch,[_6L,_YA,_9p,_10j,_YM,_10l,_])),_10t=B(A(_ch,[_6L,_YA,_9p,_10j,_YO,function(_10u,_){var _10v=E(_10i),_10w=rMV(_10v),_10x=E(_10w),_10y=B(_ZP(_10u,_10x[1],_10x[2],_10x[3],_10x[4],_10x[5],_10x[6],_10x[7],_10x[8])),_=wMV(_10v,[0,_2W,_10y[2],_10y[3],_10y[4],_10y[5],_10y[6],_10y[7],_10y[8]]);return new F(function(){return A(_10k,[_]);});},_])),_10z=B(A(_ch,[_6L,_YA,_9p,_10j,_YN,function(_10A,_){var _10B=E(_10i),_10C=rMV(_10B),_10D=E(_10C),_10E=B(_ZP(_10A,_10D[1],_10D[2],_10D[3],_10D[4],_10D[5],_10D[6],_10D[7],_10D[8])),_=wMV(_10B,[0,_10E[1],_10E[2],_10E[3],_10E[4],_10E[5],_10E[6],_10E[7],_10E[8]]);return new F(function(){return A(_10k,[_]);});},_]));return _a;},_10F=new T(function(){return document;}),_10G=function(_10H,_){var _10I=E(_10H);if(!_10I[0]){return _3n;}else{var _10J=B(_10G(_10I[2],_));return [1,_10I[1],_10J];}},_10K=function(_10L,_){var _10M=__arr2lst(0,_10L);return new F(function(){return _10G(_10M,_);});},_10N=(function(e,q){if(!e || typeof e.querySelectorAll !== 'function') {return [];} else {return e.querySelectorAll(q);}}),_10O=function(_10P,_10Q,_10R){var _10S=function(_){var _10T=E(_10N)(E(_10Q),toJSStr(E(_10R)));return new F(function(){return _10K(_10T,_);});};return new F(function(){return A(_2,[_10P,_10S]);});},_10U=(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);}),_10V=(function(x){return document.getElementById(x).value;}),_10W=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_10X=new T(function(){return B(err(_10W));}),_10Y=function(_10Z){var _110=E(_10Z);return (_110[0]==0)?E(_10X):E(_110[1]);},_111=0,_112=[0,_111,_111],_113=653,_114=[0,_113,_111],_115=986,_116=[0,_113,_115],_117=[0,_111,_115],_118=[0,_112,_117,_116,_114],_119=[0,_1Q,_118],_11a=50,_11b=5,_11c=0,_11d=function(_11e,_11f,_11g){var _11h=E(_11f),_11i=E(_11g),_11j=new T(function(){var _11k=B(_vw(_11e)),_11l=B(_11d(_11e,_11i,B(A(_tq,[_11k,new T(function(){return B(A(_up,[_11k,_11i,_11i]));}),_11h]))));return [1,_11l[1],_11l[2]];});return [0,_11h,_11j];},_11m=function(_11n){return E(E(_11n)[2]);},_11o=function(_11p){return E(E(_11p)[4]);},_11q=function(_11r){return E(E(_11r)[6]);},_11s=function(_11t,_11u){var _11v=E(_11u);if(!_11v[0]){return [0];}else{var _11w=_11v[1];return (!B(A(_11t,[_11w])))?[0]:[1,_11w,new T(function(){return B(_11s(_11t,_11v[2]));})];}},_11x=function(_11y,_11z,_11A,_11B,_11C){var _11D=B(_11d(_11z,_11A,_11B)),_11E=new T(function(){var _11F=new T(function(){return B(_vw(_11z));}),_11G=new T(function(){return B(A(_11m,[_11z,new T(function(){return B(A(_tq,[_11F,_11B,_11A]));}),new T(function(){return B(A(_tw,[_11F,_tv]));})]));});if(!B(A(_11q,[_11y,_11B,_11A]))){var _11H=new T(function(){return B(A(_up,[_11F,_11C,_11G]));});return function(_11I){return new F(function(){return A(_11q,[_11y,_11I,_11H]);});};}else{var _11J=new T(function(){return B(A(_up,[_11F,_11C,_11G]));});return function(_11K){return new F(function(){return A(_11o,[_11y,_11K,_11J]);});};}});return new F(function(){return _11s(_11E,[1,_11D[1],_11D[2]]);});},_11L=new T(function(){return B(_11x(_pm,_n7,_11c,_11b,_11a));}),_11M=function(_11N){return E(_11N)*1.7453292519943295e-2;},_11O=new T(function(){return B(_1A(_11M,_11L));}),_11P=0.5,_11Q=[0,_2W,_3n,_11c,_11a,_11c,_2M,_11P,_11O],_11R=new T(function(){return B(err(_CD));}),_11S=new T(function(){return B(unCStr("IndianRoller2.jpg"));}),_11T="loadPath",_11U="filePath",_11V=new T(function(){return B(err(_CF));}),_11W=function(_11X,_11Y){return new F(function(){return A(_11Y,[_2K]);});},_11Z=[0,_2P,_11W],_120=[1,_11Z,_3n],_121=function(_122,_123){return new F(function(){return A(_123,[_2M]);});},_124=[0,_2O,_121],_125=[1,_124,_120],_126=function(_127,_128,_129){var _12a=E(_127);if(!_12a[0]){return [2];}else{var _12b=E(_12a[1]),_12c=_12b[1],_12d=new T(function(){return B(A(_12b[2],[_128,_129]));}),_12e=new T(function(){return B(_No(function(_12f){var _12g=E(_12f);switch(_12g[0]){case 3:return (!B(_26(_12c,_12g[1])))?[2]:E(_12d);case 4:return (!B(_26(_12c,_12g[1])))?[2]:E(_12d);default:return [2];}}));}),_12h=function(_12i){return E(_12e);};return new F(function(){return _CS([1,function(_12j){return new F(function(){return A(_M5,[_12j,_12h]);});}],new T(function(){return B(_126(_12a[2],_128,_129));}));});}},_12k=function(_12l,_12m){return new F(function(){return _126(_125,_12l,_12m);});},_12n=new T(function(){return B(A(_Of,[_12k,_NV,_OZ]));}),_12o=new T(function(){return B(err(_CD));}),_12p=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:50:3-15"));}),_12q=[0,_6C,_6D,_3n,_12p,_6C,_6C],_12r=new T(function(){return B(_6A(_12q));}),_12s=new T(function(){return B(err(_CF));}),_12t=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:51:3-15"));}),_12u=[0,_6C,_6D,_3n,_12t,_6C,_6C],_12v=new T(function(){return B(_6A(_12u));}),_12w=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:52:3-11"));}),_12x=[0,_6C,_6D,_3n,_12w,_6C,_6C],_12y=new T(function(){return B(_6A(_12x));}),_12z=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:53:3-15"));}),_12A=[0,_6C,_6D,_3n,_12z,_6C,_6C],_12B=new T(function(){return B(_6A(_12A));}),_12C=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:62:3-10"));}),_12D=[0,_6C,_6D,_3n,_12C,_6C,_6C],_12E=new T(function(){return B(_6A(_12D));}),_12F=function(_12G,_12H){var _12I=function(_12J,_12K){var _12L=function(_12M){return new F(function(){return A(_12K,[new T(function(){return  -E(_12M);})]);});},_12N=new T(function(){return B(_No(function(_12O){return new F(function(){return A(_12G,[_12O,_12J,_12L]);});}));}),_12P=function(_12Q){return E(_12N);},_12R=function(_12S){return new F(function(){return A(_M5,[_12S,_12P]);});},_12T=new T(function(){return B(_No(function(_12U){var _12V=E(_12U);if(_12V[0]==4){var _12W=E(_12V[1]);if(!_12W[0]){return new F(function(){return A(_12G,[_12V,_12J,_12K]);});}else{if(E(_12W[1])==45){if(!E(_12W[2])[0]){return [1,_12R];}else{return new F(function(){return A(_12G,[_12V,_12J,_12K]);});}}else{return new F(function(){return A(_12G,[_12V,_12J,_12K]);});}}}else{return new F(function(){return A(_12G,[_12V,_12J,_12K]);});}}));}),_12X=function(_12Y){return E(_12T);};return [1,function(_12Z){return new F(function(){return A(_M5,[_12Z,_12X]);});}];};return new F(function(){return _Of(_12I,_12H);});},_130=new T(function(){return 1/0;}),_131=function(_132,_133){return new F(function(){return A(_133,[_130]);});},_134=new T(function(){return 0/0;}),_135=function(_136,_137){return new F(function(){return A(_137,[_134]);});},_138=new T(function(){return B(unCStr("NaN"));}),_139=new T(function(){return B(unCStr("Infinity"));}),_13a=function(_13b,_13c){while(1){var _13d=E(_13b);if(!_13d[0]){var _13e=E(_13d[1]);if(_13e==(-2147483648)){_13b=[1,I_fromInt(-2147483648)];continue;}else{var _13f=E(_13c);if(!_13f[0]){return [0,_13e%_13f[1]];}else{_13b=[1,I_fromInt(_13e)];_13c=_13f;continue;}}}else{var _13g=_13d[1],_13h=E(_13c);return (_13h[0]==0)?[1,I_rem(_13g,I_fromInt(_13h[1]))]:[1,I_rem(_13g,_13h[1])];}}},_13i=function(_13j,_13k){if(!B(_jl(_13k,_tu))){return new F(function(){return _13a(_13j,_13k);});}else{return E(_jg);}},_13l=function(_13m,_13n){while(1){if(!B(_jl(_13n,_tu))){var _13o=_13n,_13p=B(_13i(_13m,_13n));_13m=_13o;_13n=_13p;continue;}else{return E(_13m);}}},_13q=function(_13r){var _13s=E(_13r);if(!_13s[0]){var _13t=E(_13s[1]);return (_13t==(-2147483648))?E(_mq):(_13t<0)?[0, -_13t]:E(_13s);}else{var _13u=_13s[1];return (I_compareInt(_13u,0)>=0)?E(_13s):[1,I_negate(_13u)];}},_13v=5,_13w=new T(function(){return B(_jc(_13v));}),_13x=new T(function(){return die(_13w);}),_13y=function(_13z,_13A){if(!B(_jl(_13A,_tu))){var _13B=B(_13l(B(_13q(_13z)),B(_13q(_13A))));return (!B(_jl(_13B,_tu)))?[0,B(_xV(_13z,_13B)),B(_xV(_13A,_13B))]:E(_jg);}else{return E(_13x);}},_13C=new T(function(){return B(_jl(_tv,_tu));}),_13D=function(_13E,_13F,_13G){while(1){if(!E(_13C)){if(!B(_jl(B(_13a(_13F,_tv)),_tu))){if(!B(_jl(_13F,_q4))){var _13H=B(_sY(_13E,_13E)),_13I=B(_xV(B(_lM(_13F,_q4)),_tv)),_13J=B(_sY(_13E,_13G));_13E=_13H;_13F=_13I;_13G=_13J;continue;}else{return new F(function(){return _sY(_13E,_13G);});}}else{var _13H=B(_sY(_13E,_13E)),_13I=B(_xV(_13F,_tv));_13E=_13H;_13F=_13I;continue;}}else{return E(_jg);}}},_13K=function(_13L,_13M){while(1){if(!E(_13C)){if(!B(_jl(B(_13a(_13M,_tv)),_tu))){if(!B(_jl(_13M,_q4))){return new F(function(){return _13D(B(_sY(_13L,_13L)),B(_xV(B(_lM(_13M,_q4)),_tv)),_13L);});}else{return E(_13L);}}else{var _13N=B(_sY(_13L,_13L)),_13O=B(_xV(_13M,_tv));_13L=_13N;_13M=_13O;continue;}}else{return E(_jg);}}},_13P=function(_13Q,_13R){if(!B(_g9(_13R,_tu))){if(!B(_jl(_13R,_tu))){return new F(function(){return _13K(_13Q,_13R);});}else{return E(_q4);}}else{return E(_ub);}},_13S=[0,1],_13T=[0,0],_13U=[0,-1],_13V=function(_13W){var _13X=E(_13W);if(!_13X[0]){var _13Y=_13X[1];return (_13Y>=0)?(E(_13Y)==0)?E(_13T):E(_k3):E(_13U);}else{var _13Z=I_compareInt(_13X[1],0);return (_13Z<=0)?(E(_13Z)==0)?E(_13T):E(_13U):E(_k3);}},_140=function(_141,_142,_143){while(1){var _144=E(_143);if(!_144[0]){if(!B(_g9(_141,_FQ))){return [0,B(_sY(_142,B(_13P(_FG,_141)))),_q4];}else{var _145=B(_13P(_FG,B(_mr(_141))));return new F(function(){return _13y(B(_sY(_142,B(_13V(_145)))),B(_13q(_145)));});}}else{var _146=B(_lM(_141,_13S)),_147=B(_jw(B(_sY(_142,_FG)),B(_bO(E(_144[1])))));_141=_146;_142=_147;_143=_144[2];continue;}}},_148=function(_149,_14a){var _14b=E(_149);if(!_14b[0]){var _14c=_14b[1],_14d=E(_14a);return (_14d[0]==0)?_14c>=_14d[1]:I_compareInt(_14d[1],_14c)<=0;}else{var _14e=_14b[1],_14f=E(_14a);return (_14f[0]==0)?I_compareInt(_14e,_14f[1])>=0:I_compare(_14e,_14f[1])>=0;}},_14g=function(_14h){var _14i=E(_14h);if(!_14i[0]){var _14j=_14i[2];return new F(function(){return _13y(B(_sY(B(_FR(new T(function(){return B(_bO(E(_14i[1])));}),new T(function(){return B(_bb(_14j,0));},1),B(_1A(_FH,_14j)))),_13S)),_13S);});}else{var _14k=_14i[1],_14l=_14i[3],_14m=E(_14i[2]);if(!_14m[0]){var _14n=E(_14l);if(!_14n[0]){return new F(function(){return _13y(B(_sY(B(_G7(_FG,_14k)),_13S)),_13S);});}else{var _14o=_14n[1];if(!B(_148(_14o,_FQ))){var _14p=B(_13P(_FG,B(_mr(_14o))));return new F(function(){return _13y(B(_sY(B(_G7(_FG,_14k)),B(_13V(_14p)))),B(_13q(_14p)));});}else{return new F(function(){return _13y(B(_sY(B(_sY(B(_G7(_FG,_14k)),B(_13P(_FG,_14o)))),_13S)),_13S);});}}}else{var _14q=_14m[1],_14r=E(_14l);if(!_14r[0]){return new F(function(){return _140(_FQ,B(_G7(_FG,_14k)),_14q);});}else{return new F(function(){return _140(_14r[1],B(_G7(_FG,_14k)),_14q);});}}}},_14s=function(_14t,_14u){while(1){var _14v=E(_14u);if(!_14v[0]){return [0];}else{if(!B(A(_14t,[_14v[1]]))){return E(_14v);}else{_14u=_14v[2];continue;}}}},_14w=0,_14x=function(_14y){return new F(function(){return _sm(_14w,_14y);});},_14z=[0,E(_FQ),E(_q4)],_14A=[1,_14z],_14B=[0,-2147483648],_14C=[0,2147483647],_14D=function(_14E,_14F,_14G){var _14H=E(_14G);if(!_14H[0]){return [1,new T(function(){var _14I=B(_14g(_14H));return [0,E(_14I[1]),E(_14I[2])];})];}else{var _14J=E(_14H[3]);if(!_14J[0]){return [1,new T(function(){var _14K=B(_14g(_14H));return [0,E(_14K[1]),E(_14K[2])];})];}else{var _14L=_14J[1];if(!B(_jV(_14L,_14C))){if(!B(_g9(_14L,_14B))){var _14M=function(_14N){var _14O=_14N+B(_jt(_14L))|0;return (_14O<=(E(_14F)+3|0))?(_14O>=(E(_14E)-3|0))?[1,new T(function(){var _14P=B(_14g(_14H));return [0,E(_14P[1]),E(_14P[2])];})]:E(_14A):[0];},_14Q=B(_14s(_14x,_14H[1]));if(!_14Q[0]){var _14R=E(_14H[2]);if(!_14R[0]){return E(_14A);}else{var _14S=B(_kD(_14x,_14R[1]));if(!E(_14S[2])[0]){return E(_14A);}else{return new F(function(){return _14M( -B(_bb(_14S[1],0)));});}}}else{return new F(function(){return _14M(B(_bb(_14Q,0)));});}}else{return [0];}}else{return [0];}}}},_14T=function(_14U){var _14V=E(_14U);switch(_14V[0]){case 3:var _14W=_14V[1];return (!B(_26(_14W,_139)))?(!B(_26(_14W,_138)))?E(_OP):E(_135):E(_131);case 5:var _14X=B(_14D(_oi,_oh,_14V[1]));if(!_14X[0]){return E(_131);}else{var _14Y=new T(function(){var _14Z=E(_14X[1]);return B(_mz(_14Z[1],_14Z[2]));});return function(_150,_151){return new F(function(){return A(_151,[_14Y]);});};}break;default:return E(_OP);}},_152=new T(function(){return B(A(_12F,[_14T,_NV,_OZ]));}),_153=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:63:3-11"));}),_154=[0,_6C,_6D,_3n,_153,_6C,_6C],_155=new T(function(){return B(_6A(_154));}),_156=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:72:3-12"));}),_157=[0,_6C,_6D,_3n,_156,_6C,_6C],_158=new T(function(){return B(_6A(_157));}),_159=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:73:3-12"));}),_15a=[0,_6C,_6D,_3n,_159,_6C,_6C],_15b=new T(function(){return B(_6A(_15a));}),_15c=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:74:3-11"));}),_15d=[0,_6C,_6D,_3n,_15c,_6C,_6C],_15e=new T(function(){return B(_6A(_15d));}),_15f=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:89:3-11"));}),_15g=[0,_6C,_6D,_3n,_15f,_6C,_6C],_15h=new T(function(){return B(_6A(_15g));}),_15i=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:94:3-15"));}),_15j=[0,_6C,_6D,_3n,_15i,_6C,_6C],_15k=new T(function(){return B(_6A(_15j));}),_15l=new T(function(){return B(unCStr("value"));}),_15m=new T(function(){return B(unCStr("input[name=\'mount\']:checked"));}),_15n="offset",_15o="bottom",_15p="top",_15q="stepSize",_15r=function(_15s,_15t){return [1,new T(function(){var _15u=B(_P7(B(_CI(_152,_15s))));if(!_15u[0]){return E(_12o);}else{if(!E(_15u[2])[0]){return E(_15u[1])*1.7453292519943295e-2;}else{return E(_12s);}}}),_15t];},_15v="rotations",_15w=new T(function(){return B(unCStr("loadPath"));}),_15x=function(_15y,_){var _15z=function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);},_15A=E(_15z)("processDump",toJSStr(_15w));return new F(function(){return _eV(_);});},_15B=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:122:5-17"));}),_15C=[0,_6C,_6D,_3n,_15B,_6C,_6C],_15D=new T(function(){return B(_6A(_15C));}),_15E=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:125:5-19"));}),_15F=[0,_6C,_6D,_3n,_15E,_6C,_6C],_15G=new T(function(){return B(_6A(_15F));}),_15H=new T(function(){return B(unCStr(".txt"));}),_15I=new T(function(){return B(unCStr("download"));}),_15J=new T(function(){return B(unCStr(".json"));}),_15K="saveLink",_15L=new T(function(){return B(unCStr("filePath"));}),_15M=new T(function(){return B(unCStr("input[name=\'mount\']"));}),_15N=function(_15O,_15P){var _15Q=E(_15P);if(!_15Q[0]){return [0,_3n,_3n];}else{var _15R=_15Q[1];if(!B(A(_15O,[_15R]))){var _15S=new T(function(){var _15T=B(_15N(_15O,_15Q[2]));return [0,_15T[1],_15T[2]];});return [0,[1,_15R,new T(function(){return E(E(_15S)[1]);})],new T(function(){return E(E(_15S)[2]);})];}else{return [0,_3n,_15Q];}}},_15U=function(_15V){var _15W=_15V>>>0;if(_15W>887){var _15X=u_iswspace(_15V);return (E(_15X)==0)?false:true;}else{var _15Y=E(_15W);return (_15Y==32)?true:(_15Y-9>>>0>4)?(E(_15Y)==160)?true:false:true;}},_15Z=function(_160){return new F(function(){return _15U(E(_160));});},_161=function(_162,_163,_164){var _165=function(_166){var _167=B(_14s(_15Z,_166));if(!_167[0]){return E(_163);}else{var _168=new T(function(){var _169=B(_15N(_15Z,_167));return [0,_169[1],_169[2]];});return new F(function(){return A(_162,[new T(function(){return E(E(_168)[1]);}),new T(function(){return B(_165(E(_168)[2]));})]);});}};return new F(function(){return _165(_164);});},_16a=function(_){var _16b=B(A(_T0,[_6K,_11U,_])),_16c=E(_16b);if(!_16c[0]){return new F(function(){return die(_12r);});}else{var _16d=B(A(_T0,[_6K,_11T,_])),_16e=E(_16d);if(!_16e[0]){return new F(function(){return die(_12v);});}else{var _16f=B(A(_T0,[_6K,_15v,_])),_16g=E(_16f);if(!_16g[0]){return new F(function(){return die(_12y);});}else{var _16h=_16g[1],_16i=B(A(_T0,[_6K,_15q,_])),_16j=E(_16i);if(!_16j[0]){return new F(function(){return die(_12B);});}else{var _16k=_16j[1],_16l=nMV(_119),_16m=_16l,_16n=nMV(_11Q),_16o=_16n,_16p=B(A(_5,[_6K,_11S,_])),_16q=nMV(_16p),_16r=_16q,_16s=nMV(_11S),_16t=_16s,_16u=B(A(_T0,[_6K,_Wh,_])),_16v=E(_16u);if(!_16v[0]){return new F(function(){return die(_12E);});}else{var _16w=E(_16v[1]),_16x=E(_N),_16y=_16x(_16w);if(!_16y){return new F(function(){return die(_12E);});}else{var _16z=E(_M),_16A=_16z(_16w),_16B=_16A,_16C=B(A(_T0,[_6K,_Wd,_])),_16D=function(_,_16E){var _16F=E(_16E);if(!_16F[0]){return new F(function(){return die(_155);});}else{var _16G=function(_){return new F(function(){return _Xi(_16o,_16m,_16r,_);});},_16H=B(_Z4(_16m,[0,_16B,_16w],_16G,_)),_16I=B(_10h(_16o,_16F[1],_16G,_)),_16J=function(_16K,_){var _16L=String(E(_16K)),_16M=jsParseJSON(_16L);if(!_16M[0]){return _8Y;}else{var _16N=B(_4n(_16M[1]));if(!_16N[0]){return _8Y;}else{var _16O=_16N[1],_=wMV(_16m,new T(function(){return E(E(_16O)[1]);})),_=wMV(_16o,new T(function(){return E(E(_16O)[2]);}));return _8Y;}}},_16P=__createJSFunc(2,E(_16J)),_16Q=(function(s,f){Haste[s] = f;}),_16R=E(_16Q)("processDump",_16P),_16S=B(A(_T0,[_6K,_15p,_])),_16T=E(_16S);if(!_16T[0]){return new F(function(){return die(_158);});}else{var _16U=_16T[1],_16V=B(A(_T0,[_6K,_15o,_])),_16W=E(_16V);if(!_16W[0]){return new F(function(){return die(_15b);});}else{var _16X=_16W[1],_16Y=B(A(_T0,[_6K,_15n,_])),_16Z=E(_16Y);if(!_16Z[0]){return new F(function(){return die(_15e);});}else{var _170=_16Z[1],_171=B(A(_10O,[_6K,_10F,_15M,_])),_172=function(_173,_){var _174=E(_173),_175=toJSStr(_15L),_176=E(_10U)(_175),_177=B(A(_5,[_6K,new T(function(){var _178=String(_176);return fromJSStr(_178);}),_])),_=wMV(_16r,_177),_179=E(_10V)(_175),_17a=new T(function(){var _17b=String(_179);return fromJSStr(_17b);}),_=wMV(_16t,_17a),_17c=B(A(_T0,[_6K,_15K,_])),_17d=E(_17c);if(!_17d[0]){return new F(function(){return die(_15D);});}else{var _17e=toJSStr(E(_15I)),_17f=E(_9C),_17g=_17f(E(_17d[1]),_17e,toJSStr(B(_16(_17a,_15J)))),_17h=B(A(_T0,[_6K,_W0,_])),_17i=E(_17h);if(!_17i[0]){return new F(function(){return die(_15G);});}else{var _17j=_17f(E(_17i[1]),_17e,toJSStr(B(_16(_17a,_15H))));return new F(function(){return _Xi(_16o,_16m,_16r,_);});}}},_17k=B(A(_ch,[_6L,_S,_o,_16c[1],_bj,_172,_])),_17l=B(A(_ch,[_6L,_S,_o,_16e[1],_bj,_15x,_])),_17m=function(_){var _17n=B(A(_T0,[_6K,_15v,_])),_17o=E(_17n);if(!_17o[0]){return new F(function(){return die(_15h);});}else{var _17p=B(A(_WM,[_S,_6K,_17o[1],_15l,_])),_17q=rMV(_16o),_17r=E(_17q),_=wMV(_16o,[0,_17r[1],_17r[2],_17r[3],_17r[4],_17r[5],_17r[6],_17r[7],new T(function(){return B(_161(_15r,_3n,_17p));})]),_17s=B(A(_T0,[_6K,_15q,_])),_17t=E(_17s);if(!_17t[0]){return new F(function(){return die(_15k);});}else{var _17u=B(A(_WM,[_S,_6K,_17t[1],_15l,_])),_17v=rMV(_16o),_17w=E(_17v),_=wMV(_16o,[0,_17w[1],_17w[2],_17w[3],_17w[4],_17w[5],_17w[6],new T(function(){var _17x=B(_P7(B(_CI(_152,_17u))));if(!_17x[0]){return E(_12o);}else{if(!E(_17x[2])[0]){return E(_17x[1]);}else{return E(_12s);}}}),_17w[8]]),_17y=B(A(_T0,[_6K,_15p,_])),_17z=B(A(_WM,[_S,_6K,new T(function(){return B(_10Y(_17y));}),_15l,_])),_17A=B(A(_T0,[_6K,_15o,_])),_17B=B(A(_WM,[_S,_6K,new T(function(){return B(_10Y(_17A));}),_15l,_])),_17C=B(A(_T0,[_6K,_15n,_])),_17D=B(A(_WM,[_S,_6K,new T(function(){return B(_10Y(_17C));}),_15l,_])),_17E=B(A(_10O,[_6K,_10F,_15m,_])),_17F=E(_17E);if(!_17F[0]){return new F(function(){return _Yt(_);});}else{if(!E(_17F[2])[0]){var _17G=B(A(_WM,[_S,_6K,_17F[1],_15l,_])),_17H=rMV(_16o),_17I=E(_17H),_=wMV(_16o,[0,_17I[1],_17I[2],new T(function(){var _17J=B(_P7(B(_CI(_152,_17z))));if(!_17J[0]){return E(_12o);}else{if(!E(_17J[2])[0]){return E(_17J[1]);}else{return E(_12s);}}}),new T(function(){var _17K=B(_P7(B(_CI(_152,_17B))));if(!_17K[0]){return E(_12o);}else{if(!E(_17K[2])[0]){return E(_17K[1]);}else{return E(_12s);}}}),new T(function(){var _17L=B(_P7(B(_CI(_152,_17D))));if(!_17L[0]){return E(_12o);}else{if(!E(_17L[2])[0]){return E(_17L[1]);}else{return E(_12s);}}}),new T(function(){var _17M=B(_P7(B(_CI(_12n,_17G))));if(!_17M[0]){return E(_11R);}else{if(!E(_17M[2])[0]){return E(_17M[1]);}else{return E(_11V);}}}),_17I[7],_17I[8]]);return new F(function(){return _Xi(_16o,_16m,_16r,_);});}else{return new F(function(){return _Yt(_);});}}}}},_17N=function(_17O,_){return new F(function(){return _17m(_);});},_17P=function(_17Q,_){while(1){var _17R=E(_17Q);if(!_17R[0]){var _17S=B(A(_ch,[_6L,_S,_o,_16k,_bj,_17N,_])),_17T=B(A(_ch,[_6L,_S,_o,_16h,_bj,_17N,_])),_17U=B(A(_ch,[_6L,_S,_o,_16U,_bj,_17N,_])),_17V=B(A(_ch,[_6L,_S,_o,_16X,_bj,_17N,_])),_17W=B(A(_ch,[_6L,_S,_o,_170,_bj,_17N,_]));return _a;}else{var _17X=B(A(_ch,[_6L,_S,_o,_17R[1],_bj,_17N,_]));_17Q=_17R[2];continue;}}},_17Y=B(_17P(_171,_)),_17Z=B(A(_ch,[_6L,_S,_L,_16k,_Yu,_17N,_])),_180=B(A(_ch,[_6L,_S,_L,_16h,_Yu,_17N,_])),_181=B(A(_ch,[_6L,_S,_L,_16U,_Yu,_17N,_])),_182=B(A(_ch,[_6L,_S,_L,_16X,_Yu,_17N,_])),_183=B(A(_ch,[_6L,_S,_L,_170,_Yu,_17N,_]));return new F(function(){return _Xi(_16o,_16m,_16r,_);});}}}}},_184=E(_16C);if(!_184[0]){return new F(function(){return _16D(_,_6C);});}else{var _185=E(_184[1]),_186=_16x(_185);if(!_186){return new F(function(){return _16D(_,_6C);});}else{var _187=_16z(_185);return new F(function(){return _16D(_,[1,[0,_187,_185]]);});}}}}}}}}},_188=function(_){return new F(function(){return _16a(_);});};
var hasteMain = function() {B(A(_188, [0]));};window.onload = hasteMain;