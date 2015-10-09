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

var _0="src",_1=(function(e,p,v){e[p] = v;}),_2=function(_3){return E(E(_3)[2]);},_4=(function(t){return document.createElement(t);}),_5=function(_6,_7){return new F(function(){return A(_2,[_6,function(_){var _8=E(_4)("img"),_9=E(_1)(_8,E(_0),toJSStr(E(_7)));return _8;}]);});},_a=0,_b=function(_){return _a;},_c=function(_d,_e,_){return new F(function(){return _b(_);});},_f="scroll",_g="submit",_h="blur",_i="focus",_j="change",_k="unload",_l="load",_m=function(_n){switch(E(_n)){case 0:return E(_l);case 1:return E(_k);case 2:return E(_j);case 3:return E(_i);case 4:return E(_h);case 5:return E(_g);default:return E(_f);}},_o=[0,_m,_c],_p="metaKey",_q="shiftKey",_r="altKey",_s="ctrlKey",_t="keyCode",_u=function(_v,_){var _w=_v[E(_t)],_x=_v[E(_s)],_y=_v[E(_r)],_z=_v[E(_q)],_A=_v[E(_p)];return new T(function(){var _B=Number(_w),_C=jsTrunc(_B);return [0,_C,E(_x),E(_y),E(_z),E(_A)];});},_D=function(_E,_F,_){return new F(function(){return _u(E(_F),_);});},_G="keydown",_H="keyup",_I="keypress",_J=function(_K){switch(E(_K)){case 0:return E(_I);case 1:return E(_H);default:return E(_G);}},_L=[0,_J,_D],_M=(function(e){return e.getContext('2d');}),_N=(function(e){return !!e.getContext;}),_O=function(_P,_){return [1,_P];},_Q=function(_R){return E(_R);},_S=[0,_Q,_O],_T=function(_U){return E(E(_U)[1]);},_V=function(_W,_X){return (!B(A(_T,[_Y,_W,_X])))?true:false;},_Z=function(_10,_11){var _12=strEq(E(_10),E(_11));return (E(_12)==0)?false:true;},_13=function(_14,_15){return new F(function(){return _Z(_14,_15);});},_Y=new T(function(){return [0,_13,_V];}),_16=function(_17,_18){var _19=E(_17);return (_19[0]==0)?E(_18):[1,_19[1],new T(function(){return B(_16(_19[2],_18));})];},_1a=new T(function(){return B(unCStr("!!: negative index"));}),_1b=new T(function(){return B(unCStr("Prelude."));}),_1c=new T(function(){return B(_16(_1b,_1a));}),_1d=new T(function(){return B(err(_1c));}),_1e=new T(function(){return B(unCStr("!!: index too large"));}),_1f=new T(function(){return B(_16(_1b,_1e));}),_1g=new T(function(){return B(err(_1f));}),_1h=function(_1i,_1j){while(1){var _1k=E(_1i);if(!_1k[0]){return E(_1g);}else{var _1l=E(_1j);if(!_1l){return E(_1k[1]);}else{_1i=_1k[2];_1j=_1l-1|0;continue;}}}},_1m=function(_1n,_1o){if(_1o>=0){return new F(function(){return _1h(_1n,_1o);});}else{return E(_1d);}},_1p=new T(function(){return B(unCStr(": empty list"));}),_1q=function(_1r){return new F(function(){return err(B(_16(_1b,new T(function(){return B(_16(_1r,_1p));},1))));});},_1s=new T(function(){return B(unCStr("head"));}),_1t=new T(function(){return B(_1q(_1s));}),_1u=function(_1v){var _1w=E(_1v);if(_1w[0]==3){var _1x=E(_1w[1]);if(!_1x[0]){return E(_1t);}else{var _1y=E(_1x[1]);if(!_1y[0]){var _1z=B(_1m(_1x,1));return (_1z[0]==0)?[1,[0,_1y[1],_1z[1]]]:[0];}else{return [0];}}}else{return [0];}},_1A=function(_1B,_1C){var _1D=E(_1C);return (_1D[0]==0)?[0]:[1,new T(function(){return B(A(_1B,[_1D[1]]));}),new T(function(){return B(_1A(_1B,_1D[2]));})];},_1E=function(_1F){var _1G=E(_1F);if(_1G[0]==3){var _1H=B(_1A(_1u,_1G[1]));if(!_1H[0]){return E(_1t);}else{var _1I=E(_1H[1]);if(!_1I[0]){return [0];}else{var _1J=B(_1m(_1H,1));if(!_1J[0]){return [0];}else{var _1K=B(_1m(_1H,2));if(!_1K[0]){return [0];}else{var _1L=B(_1m(_1H,3));return (_1L[0]==0)?[0]:[1,[0,_1I[1],_1J[1],_1K[1],_1L[1]]];}}}}}else{return [0];}},_1M="box",_1N="mouse",_1O="corner",_1P="Dragging",_1Q=[0],_1R=[1,_1Q],_1S="Free",_1T="state",_1U=1,_1V=[1,_1U],_1W=0,_1X=[1,_1W],_1Y=3,_1Z=[1,_1Y],_20=2,_21=[1,_20],_22=new T(function(){return B(unCStr("SW"));}),_23=new T(function(){return B(unCStr("SE"));}),_24=new T(function(){return B(unCStr("NW"));}),_25=new T(function(){return B(unCStr("NE"));}),_26=function(_27,_28){while(1){var _29=E(_27);if(!_29[0]){return (E(_28)[0]==0)?true:false;}else{var _2a=E(_28);if(!_2a[0]){return false;}else{if(E(_29[1])!=E(_2a[1])){return false;}else{_27=_29[2];_28=_2a[2];continue;}}}}},_2b=function(_2c){var _2d=E(_2c);if(_2d[0]==1){var _2e=fromJSStr(_2d[1]);return (!B(_26(_2e,_25)))?(!B(_26(_2e,_24)))?(!B(_26(_2e,_23)))?(!B(_26(_2e,_22)))?[0]:E(_21):E(_1Z):E(_1X):E(_1V);}else{return [0];}},_2f=function(_2g,_2h,_2i){while(1){var _2j=E(_2i);if(!_2j[0]){return [0];}else{var _2k=E(_2j[1]);if(!B(A(_T,[_2g,_2h,_2k[1]]))){_2i=_2j[2];continue;}else{return [1,_2k[2]];}}}},_2l=function(_2m){var _2n=E(_2m);if(_2n[0]==4){var _2o=_2n[1],_2p=B(_2f(_Y,_1T,_2o));if(!_2p[0]){return [0];}else{var _2q=E(_2p[1]);if(_2q[0]==1){var _2r=_2q[1],_2s=strEq(_2r,E(_1S));if(!E(_2s)){var _2t=strEq(_2r,E(_1P));if(!E(_2t)){return [0];}else{var _2u=B(_2f(_Y,_1O,_2o));if(!_2u[0]){return [0];}else{var _2v=B(_2b(_2u[1]));return (_2v[0]==0)?[0]:[1,[1,_2v[1]]];}}}else{return E(_1R);}}else{return [0];}}}else{return [0];}},_2w=function(_2x){var _2y=E(_2x);if(_2y[0]==4){var _2z=_2y[1],_2A=B(_2f(_Y,_1N,_2z));if(!_2A[0]){return [0];}else{var _2B=B(_2l(_2A[1]));if(!_2B[0]){return [0];}else{var _2C=B(_2f(_Y,_1M,_2z));if(!_2C[0]){return [0];}else{var _2D=B(_1E(_2C[1]));return (_2D[0]==0)?[0]:[1,[0,_2B[1],_2D[1]]];}}}}else{return [0];}},_2E=function(_2F){return [0,E(_2F)];},_2G=function(_2H){var _2I=E(_2H);return (_2I[0]==0)?[1,_2I[1]]:[0];},_2J=[0,_2E,_2G],_2K=1,_2L=[1,_2K],_2M=0,_2N=[1,_2M],_2O=new T(function(){return B(unCStr("Top"));}),_2P=new T(function(){return B(unCStr("Bottom"));}),_2Q=function(_2R){var _2S=E(_2R);if(_2S[0]==1){var _2T=fromJSStr(_2S[1]);return (!B(_26(_2T,_2P)))?(!B(_26(_2T,_2O)))?[0]:E(_2N):E(_2L);}else{return [0];}},_2U=1,_2V=[1,_2U],_2W=0,_2X=[1,_2W],_2Y=new T(function(){return B(unCStr("Free"));}),_2Z=new T(function(){return B(unCStr("Dragging"));}),_30=function(_31){var _32=E(_31);if(_32[0]==1){var _33=fromJSStr(_32[1]);return (!B(_26(_33,_2Z)))?(!B(_26(_33,_2Y)))?[0]:E(_2X):E(_2V);}else{return [0];}},_34="title",_35="points",_36=function(_37){var _38=E(_37);if(_38[0]==4){var _39=_38[1],_3a=B(_2f(_Y,_35,_39));if(!_3a[0]){return [0];}else{var _3b=E(_3a[1]);if(_3b[0]==3){var _3c=E(_3b[1]);if(!_3c[0]){return E(_1t);}else{var _3d=E(_3c[1]);if(_3d[0]==3){var _3e=E(_3d[1]);if(!_3e[0]){return E(_1t);}else{var _3f=E(_3e[1]);if(!_3f[0]){var _3g=B(_1m(_3e,1));if(!_3g[0]){var _3h=B(_1m(_3c,1));if(_3h[0]==3){var _3i=E(_3h[1]);if(!_3i[0]){return E(_1t);}else{var _3j=E(_3i[1]);if(!_3j[0]){var _3k=B(_1m(_3i,1));if(!_3k[0]){var _3l=B(_2f(_Y,_34,_39));if(!_3l[0]){return [0];}else{var _3m=E(_3l[1]);return (_3m[0]==1)?[1,[0,[0,_3f[1],_3g[1]],[0,_3j[1],_3k[1]],new T(function(){return fromJSStr(_3m[1]);})]]:[0];}}else{return [0];}}else{return [0];}}}else{return [0];}}else{return [0];}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}},_3n=[0],_3o=function(_3p){var _3q=new T(function(){var _3r=E(E(_3p)[2]);return [3,[1,new T(function(){return B(_2E(_3r[1]));}),[1,new T(function(){return B(_2E(_3r[2]));}),_3n]]];}),_3s=new T(function(){var _3t=E(E(_3p)[1]);return [3,[1,new T(function(){return B(_2E(_3t[1]));}),[1,new T(function(){return B(_2E(_3t[2]));}),_3n]]];});return [1,[0,_34,new T(function(){return [1,toJSStr(E(E(_3p)[3]))];})],[1,[0,_35,[3,[1,_3s,[1,_3q,_3n]]]],_3n]];},_3u=function(_3v){return [4,E(B(_3o(_3v)))];},_3w=[0,_3u,_36],_3x="rotations",_3y="choice",_3z="offset",_3A="bottom",_3B="top",_3C="fileName",_3D="scans",_3E="mouse",_3F=[1,_3n],_3G=function(_3H){return E(E(_3H)[2]);},_3I=function(_3J,_3K){var _3L=E(_3K);if(_3L[0]==3){var _3M=new T(function(){return B(_3G(_3J));}),_3N=function(_3O){var _3P=E(_3O);if(!_3P[0]){return E(_3F);}else{var _3Q=B(A(_3M,[_3P[1]]));if(!_3Q[0]){return [0];}else{var _3R=B(_3N(_3P[2]));return (_3R[0]==0)?[0]:[1,[1,_3Q[1],_3R[1]]];}}};return new F(function(){return _3N(_3L[1]);});}else{return [0];}},_3S=function(_3T){var _3U=E(_3T);if(_3U[0]==4){var _3V=_3U[1],_3W=B(_2f(_Y,_3E,_3V));if(!_3W[0]){return [0];}else{var _3X=B(_30(_3W[1]));if(!_3X[0]){return [0];}else{var _3Y=B(_2f(_Y,_3D,_3V));if(!_3Y[0]){return [0];}else{var _3Z=B(_3I(_3w,_3Y[1]));if(!_3Z[0]){return [0];}else{var _40=B(_2f(_Y,_3C,_3V));if(!_40[0]){return [0];}else{var _41=E(_40[1]);if(_41[0]==1){var _42=B(_2f(_Y,_3B,_3V));if(!_42[0]){return [0];}else{var _43=E(_42[1]);if(!_43[0]){var _44=B(_2f(_Y,_3A,_3V));if(!_44[0]){return [0];}else{var _45=E(_44[1]);if(!_45[0]){var _46=B(_2f(_Y,_3z,_3V));if(!_46[0]){return [0];}else{var _47=E(_46[1]);if(!_47[0]){var _48=B(_2f(_Y,_3y,_3V));if(!_48[0]){return [0];}else{var _49=B(_2Q(_48[1]));if(!_49[0]){return [0];}else{var _4a=B(_2f(_Y,_3x,_3V));if(!_4a[0]){return [0];}else{var _4b=B(_3I(_2J,_4a[1]));return (_4b[0]==0)?[0]:[1,[0,_3X[1],_3Z[1],new T(function(){return fromJSStr(_41[1]);}),_43[1],_45[1],_47[1],_49[1],_4b[1]]];}}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}else{return [0];}}}}}}}else{return [0];}},_4c="scans",_4d="calib",_4e=function(_4f){var _4g=E(_4f);if(_4g[0]==4){var _4h=_4g[1],_4i=B(_2f(_Y,_4d,_4h));if(!_4i[0]){return [0];}else{var _4j=B(_2w(_4i[1]));if(!_4j[0]){return [0];}else{var _4k=B(_2f(_Y,_4c,_4h));if(!_4k[0]){return [0];}else{var _4l=B(_3S(_4k[1]));return (_4l[0]==0)?[0]:[1,[0,_4j[1],_4l[1]]];}}}}else{return [0];}},_4m=function(_4n,_4o,_){var _4p=B(A(_4n,[_])),_4q=B(A(_4o,[_]));return _4p;},_4r=function(_4s,_4t,_){var _4u=B(A(_4s,[_])),_4v=B(A(_4t,[_]));return new T(function(){return B(A(_4u,[_4v]));});},_4w=function(_4x,_4y,_){var _4z=B(A(_4y,[_]));return _4x;},_4A=function(_4B,_4C,_){var _4D=B(A(_4C,[_]));return new T(function(){return B(A(_4B,[_4D]));});},_4E=[0,_4A,_4w],_4F=function(_4G,_){return _4G;},_4H=function(_4I,_4J,_){var _4K=B(A(_4I,[_]));return new F(function(){return A(_4J,[_]);});},_4L=[0,_4E,_4F,_4r,_4H,_4m],_4M=function(_4N,_4O,_){var _4P=B(A(_4N,[_]));return new F(function(){return A(_4O,[_4P,_]);});},_4Q=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_4R=new T(function(){return B(unCStr("base"));}),_4S=new T(function(){return B(unCStr("IOException"));}),_4T=new T(function(){var _4U=hs_wordToWord64(4053623282),_4V=hs_wordToWord64(3693590983);return [0,_4U,_4V,[0,_4U,_4V,_4R,_4Q,_4S],_3n,_3n];}),_4W=function(_4X){return E(_4T);},_4Y=function(_4Z){return E(E(_4Z)[1]);},_50=function(_51,_52,_53){var _54=B(A(_51,[_])),_55=B(A(_52,[_])),_56=hs_eqWord64(_54[1],_55[1]);if(!_56){return [0];}else{var _57=hs_eqWord64(_54[2],_55[2]);return (!_57)?[0]:[1,_53];}},_58=function(_59){var _5a=E(_59);return new F(function(){return _50(B(_4Y(_5a[1])),_4W,_5a[2]);});},_5b=new T(function(){return B(unCStr(": "));}),_5c=new T(function(){return B(unCStr(")"));}),_5d=new T(function(){return B(unCStr(" ("));}),_5e=new T(function(){return B(unCStr("interrupted"));}),_5f=new T(function(){return B(unCStr("system error"));}),_5g=new T(function(){return B(unCStr("unsatisified constraints"));}),_5h=new T(function(){return B(unCStr("user error"));}),_5i=new T(function(){return B(unCStr("permission denied"));}),_5j=new T(function(){return B(unCStr("illegal operation"));}),_5k=new T(function(){return B(unCStr("end of file"));}),_5l=new T(function(){return B(unCStr("resource exhausted"));}),_5m=new T(function(){return B(unCStr("resource busy"));}),_5n=new T(function(){return B(unCStr("does not exist"));}),_5o=new T(function(){return B(unCStr("already exists"));}),_5p=new T(function(){return B(unCStr("resource vanished"));}),_5q=new T(function(){return B(unCStr("timeout"));}),_5r=new T(function(){return B(unCStr("unsupported operation"));}),_5s=new T(function(){return B(unCStr("hardware fault"));}),_5t=new T(function(){return B(unCStr("inappropriate type"));}),_5u=new T(function(){return B(unCStr("invalid argument"));}),_5v=new T(function(){return B(unCStr("failed"));}),_5w=new T(function(){return B(unCStr("protocol error"));}),_5x=function(_5y,_5z){switch(E(_5y)){case 0:return new F(function(){return _16(_5o,_5z);});break;case 1:return new F(function(){return _16(_5n,_5z);});break;case 2:return new F(function(){return _16(_5m,_5z);});break;case 3:return new F(function(){return _16(_5l,_5z);});break;case 4:return new F(function(){return _16(_5k,_5z);});break;case 5:return new F(function(){return _16(_5j,_5z);});break;case 6:return new F(function(){return _16(_5i,_5z);});break;case 7:return new F(function(){return _16(_5h,_5z);});break;case 8:return new F(function(){return _16(_5g,_5z);});break;case 9:return new F(function(){return _16(_5f,_5z);});break;case 10:return new F(function(){return _16(_5w,_5z);});break;case 11:return new F(function(){return _16(_5v,_5z);});break;case 12:return new F(function(){return _16(_5u,_5z);});break;case 13:return new F(function(){return _16(_5t,_5z);});break;case 14:return new F(function(){return _16(_5s,_5z);});break;case 15:return new F(function(){return _16(_5r,_5z);});break;case 16:return new F(function(){return _16(_5q,_5z);});break;case 17:return new F(function(){return _16(_5p,_5z);});break;default:return new F(function(){return _16(_5e,_5z);});}},_5A=new T(function(){return B(unCStr("}"));}),_5B=new T(function(){return B(unCStr("{handle: "));}),_5C=function(_5D,_5E,_5F,_5G,_5H,_5I){var _5J=new T(function(){var _5K=new T(function(){var _5L=new T(function(){var _5M=E(_5G);if(!_5M[0]){return E(_5I);}else{var _5N=new T(function(){return B(_16(_5M,new T(function(){return B(_16(_5c,_5I));},1)));},1);return B(_16(_5d,_5N));}},1);return B(_5x(_5E,_5L));}),_5O=E(_5F);if(!_5O[0]){return E(_5K);}else{return B(_16(_5O,new T(function(){return B(_16(_5b,_5K));},1)));}}),_5P=E(_5H);if(!_5P[0]){var _5Q=E(_5D);if(!_5Q[0]){return E(_5J);}else{var _5R=E(_5Q[1]);if(!_5R[0]){var _5S=new T(function(){var _5T=new T(function(){return B(_16(_5A,new T(function(){return B(_16(_5b,_5J));},1)));},1);return B(_16(_5R[1],_5T));},1);return new F(function(){return _16(_5B,_5S);});}else{var _5U=new T(function(){var _5V=new T(function(){return B(_16(_5A,new T(function(){return B(_16(_5b,_5J));},1)));},1);return B(_16(_5R[1],_5V));},1);return new F(function(){return _16(_5B,_5U);});}}}else{return new F(function(){return _16(_5P[1],new T(function(){return B(_16(_5b,_5J));},1));});}},_5W=function(_5X){var _5Y=E(_5X);return new F(function(){return _5C(_5Y[1],_5Y[2],_5Y[3],_5Y[4],_5Y[6],_3n);});},_5Z=function(_60,_61,_62){var _63=E(_61);return new F(function(){return _5C(_63[1],_63[2],_63[3],_63[4],_63[6],_62);});},_64=function(_65,_66){var _67=E(_65);return new F(function(){return _5C(_67[1],_67[2],_67[3],_67[4],_67[6],_66);});},_68=44,_69=93,_6a=91,_6b=function(_6c,_6d,_6e){var _6f=E(_6d);if(!_6f[0]){return new F(function(){return unAppCStr("[]",_6e);});}else{var _6g=new T(function(){var _6h=new T(function(){var _6i=function(_6j){var _6k=E(_6j);if(!_6k[0]){return [1,_69,_6e];}else{var _6l=new T(function(){return B(A(_6c,[_6k[1],new T(function(){return B(_6i(_6k[2]));})]));});return [1,_68,_6l];}};return B(_6i(_6f[2]));});return B(A(_6c,[_6f[1],_6h]));});return [1,_6a,_6g];}},_6m=function(_6n,_6o){return new F(function(){return _6b(_64,_6n,_6o);});},_6p=[0,_5Z,_5W,_6m],_6q=new T(function(){return [0,_4W,_6p,_6r,_58,_5W];}),_6r=function(_6s){return [0,_6q,_6s];},_6t=[0],_6u=7,_6v=function(_6w){return [0,_6t,_6u,_3n,_6w,_6t,_6t];},_6x=function(_6y,_){var _6z=new T(function(){return B(_6r(new T(function(){return B(_6v(_6y));})));});return new F(function(){return die(_6z);});},_6A=[0,_4L,_4M,_4H,_4F,_6x],_6B=[0,_6A,_Q],_6C=[0,_6B,_4F],_6D=function(_6E,_6F,_6G,_6H,_6I,_6J,_6K,_6L){if(_6E!=_6I){return false;}else{if(E(_6F)!=E(_6J)){return false;}else{var _6M=E(_6G),_6N=E(_6K);if(E(_6M[1])!=E(_6N[1])){return false;}else{if(E(_6M[2])!=E(_6N[2])){return false;}else{return new F(function(){return _26(_6H,_6L);});}}}}},_6O=function(_6P,_6Q){var _6R=E(_6P),_6S=E(_6R[1]),_6T=E(_6Q),_6U=E(_6T[1]);return new F(function(){return _6D(E(_6S[1]),_6S[2],_6R[2],_6R[3],E(_6U[1]),_6U[2],_6T[2],_6T[3]);});},_6V="scans",_6W=[1,_6V,_3n],_6X="calib",_6Y=[1,_6X,_6W],_6Z=function(_70){var _71=E(_70);return [3,[1,new T(function(){return B(_2E(_71[1]));}),[1,new T(function(){return B(_2E(_71[2]));}),_3n]]];},_72=new T(function(){return [1,"Dragging"];}),_73=[0,_1T,_72],_74=new T(function(){return [1,"Free"];}),_75="state",_76=[0,_75,_74],_77=[1,_76,_3n],_78=[4,E(_77)],_79=function(_7a,_7b){switch(E(_7a)){case 0:return new F(function(){return _16(_24,_7b);});break;case 1:return new F(function(){return _16(_25,_7b);});break;case 2:return new F(function(){return _16(_22,_7b);});break;default:return new F(function(){return _16(_23,_7b);});}},_7c=function(_7d){return E(toJSStr(B(_79(_7d,_3n))));},_7e=function(_7f){return [1,B(_7c(_7f))];},_7g=function(_7h){var _7i=new T(function(){var _7j=E(E(_7h)[2]);return [3,[1,new T(function(){return B(_6Z(_7j[1]));}),[1,new T(function(){return B(_6Z(_7j[2]));}),[1,new T(function(){return B(_6Z(_7j[3]));}),[1,new T(function(){return B(_6Z(_7j[4]));}),_3n]]]]];}),_7k=new T(function(){var _7l=E(E(_7h)[1]);if(!_7l[0]){return E(_78);}else{return [4,[1,_73,[1,[0,_1O,new T(function(){return B(_7e(_7l[1]));})],_3n]]];}});return [1,[0,_1N,_7k],[1,[0,_1M,_7i],_3n]];},_7m="rotations",_7n=[1,_7m,_3n],_7o="choice",_7p=[1,_7o,_7n],_7q="offset",_7r=[1,_7q,_7p],_7s="bottom",_7t=[1,_7s,_7r],_7u="top",_7v=[1,_7u,_7t],_7w="fileName",_7x=[1,_7w,_7v],_7y="scans",_7z=[1,_7y,_7x],_7A="mouse",_7B=[1,_7A,_7z],_7C=function(_7D,_7E){var _7F=E(_7D);if(!_7F[0]){return [0];}else{var _7G=E(_7E);return (_7G[0]==0)?[0]:[1,[0,_7F[1],_7G[1]],new T(function(){return B(_7C(_7F[2],_7G[2]));})];}},_7H=function(_7I){return new F(function(){return _7C(_7B,[1,new T(function(){if(!E(E(_7I)[1])){return [1,toJSStr(E(_2Y))];}else{return [1,toJSStr(E(_2Z))];}}),[1,new T(function(){return [3,E(B(_1A(_3u,E(_7I)[2])))];}),[1,new T(function(){return [1,toJSStr(E(E(_7I)[3]))];}),[1,new T(function(){return [0,E(E(_7I)[4])];}),[1,new T(function(){return [0,E(E(_7I)[5])];}),[1,new T(function(){return [0,E(E(_7I)[6])];}),[1,new T(function(){if(!E(E(_7I)[7])){return [1,toJSStr(E(_2O))];}else{return [1,toJSStr(E(_2P))];}}),[1,new T(function(){return [3,E(B(_1A(_2E,E(_7I)[8])))];}),_3n]]]]]]]]);});},_7J=function(_7K){return [1,E(_7K)];},_7L="deltaZ",_7M="deltaY",_7N="deltaX",_7O=function(_7P,_7Q){var _7R=jsShowI(_7P);return new F(function(){return _16(fromJSStr(_7R),_7Q);});},_7S=41,_7T=40,_7U=function(_7V,_7W,_7X){if(_7W>=0){return new F(function(){return _7O(_7W,_7X);});}else{if(_7V<=6){return new F(function(){return _7O(_7W,_7X);});}else{return [1,_7T,new T(function(){var _7Y=jsShowI(_7W);return B(_16(fromJSStr(_7Y),[1,_7S,_7X]));})];}}},_7Z=new T(function(){return B(unCStr(")"));}),_80=new T(function(){return B(_7U(0,2,_7Z));}),_81=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_80));}),_82=function(_83){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_7U(0,_83,_81));}))));});},_84=function(_85,_){return new T(function(){var _86=Number(E(_85)),_87=jsTrunc(_86);if(_87<0){return B(_82(_87));}else{if(_87>2){return B(_82(_87));}else{return _87;}}});},_88=0,_89=[0,_88,_88,_88],_8a="button",_8b=new T(function(){return jsGetMouseCoords;}),_8c=function(_8d,_){var _8e=E(_8d);if(!_8e[0]){return _3n;}else{var _8f=B(_8c(_8e[2],_));return [1,new T(function(){var _8g=Number(E(_8e[1]));return jsTrunc(_8g);}),_8f];}},_8h=function(_8i,_){var _8j=__arr2lst(0,_8i);return new F(function(){return _8c(_8j,_);});},_8k=function(_8l,_){return new F(function(){return _8h(E(_8l),_);});},_8m=function(_8n,_){return new T(function(){var _8o=Number(E(_8n));return jsTrunc(_8o);});},_8p=[0,_8m,_8k],_8q=function(_8r,_){var _8s=E(_8r);if(!_8s[0]){return _3n;}else{var _8t=B(_8q(_8s[2],_));return [1,_8s[1],_8t];}},_8u=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_8v=[0,_6t,_6u,_3n,_8u,_6t,_6t],_8w=new T(function(){return B(_6r(_8v));}),_8x=function(_){return new F(function(){return die(_8w);});},_8y=function(_8z){return E(E(_8z)[1]);},_8A=function(_8B,_8C,_8D,_){var _8E=__arr2lst(0,_8D),_8F=B(_8q(_8E,_)),_8G=E(_8F);if(!_8G[0]){return new F(function(){return _8x(_);});}else{var _8H=E(_8G[2]);if(!_8H[0]){return new F(function(){return _8x(_);});}else{if(!E(_8H[2])[0]){var _8I=B(A(_8y,[_8B,_8G[1],_])),_8J=B(A(_8y,[_8C,_8H[1],_]));return [0,_8I,_8J];}else{return new F(function(){return _8x(_);});}}}},_8K=function(_){return new F(function(){return __jsNull();});},_8L=function(_8M){var _8N=B(A(_8M,[_]));return E(_8N);},_8O=new T(function(){return B(_8L(_8K));}),_8P=new T(function(){return E(_8O);}),_8Q=function(_8R,_8S,_){if(E(_8R)==7){var _8T=E(_8b)(_8S),_8U=B(_8A(_8p,_8p,_8T,_)),_8V=_8S[E(_7N)],_8W=_8S[E(_7M)],_8X=_8S[E(_7L)];return new T(function(){return [0,E(_8U),E(_6t),[0,_8V,_8W,_8X]];});}else{var _8Y=E(_8b)(_8S),_8Z=B(_8A(_8p,_8p,_8Y,_)),_90=_8S[E(_8a)],_91=__eq(_90,E(_8P));if(!E(_91)){var _92=B(_84(_90,_));return new T(function(){return [0,E(_8Z),[1,_92],E(_89)];});}else{return new T(function(){return [0,E(_8Z),E(_6t),E(_89)];});}}},_93=function(_94,_95,_){return new F(function(){return _8Q(_94,E(_95),_);});},_96="mouseout",_97="mouseover",_98="mousemove",_99="mouseup",_9a="mousedown",_9b="dblclick",_9c="click",_9d="wheel",_9e=function(_9f){switch(E(_9f)){case 0:return E(_9c);case 1:return E(_9b);case 2:return E(_9a);case 3:return E(_99);case 4:return E(_98);case 5:return E(_97);case 6:return E(_96);default:return E(_9d);}},_9g=[0,_9e,_93],_9h=function(_){return new F(function(){return E(_4)("td");});},_9i=function(_9j){return E(E(_9j)[1]);},_9k=function(_9l){return E(E(_9l)[3]);},_9m=function(_9n){return E(E(_9n)[2]);},_9o=function(_9p){return E(E(_9p)[4]);},_9q=(function(c,p){p.appendChild(c);}),_9r=function(_9s){return E(E(_9s)[1]);},_9t=(function(e,p,v){e.setAttribute(p, v);}),_9u=(function(e,p,v){e.style[p] = v;}),_9v=function(_9w,_9x,_9y,_9z){var _9A=new T(function(){return B(A(_9r,[_9w,_9y]));}),_9B=function(_9C,_){var _9D=E(_9C);if(!_9D[0]){return _a;}else{var _9E=E(_9A),_9F=E(_9q),_9G=_9F(E(_9D[1]),_9E),_9H=_9D[2];while(1){var _9I=E(_9H);if(!_9I[0]){return _a;}else{var _9J=_9F(E(_9I[1]),_9E);_9H=_9I[2];continue;}}}},_9K=function(_9L,_){while(1){var _9M=B((function(_9N,_){var _9O=E(_9N);if(!_9O[0]){return _a;}else{var _9P=_9O[2],_9Q=E(_9O[1]);if(!_9Q[0]){var _9R=_9Q[2],_9S=E(_9Q[1]);switch(_9S[0]){case 0:var _9T=E(_9A),_9U=E(_1),_9V=_9U(_9T,_9S[1],_9R),_9W=_9P;while(1){var _9X=E(_9W);if(!_9X[0]){return _a;}else{var _9Y=_9X[2],_9Z=E(_9X[1]);if(!_9Z[0]){var _a0=_9Z[2],_a1=E(_9Z[1]);switch(_a1[0]){case 0:var _a2=_9U(_9T,_a1[1],_a0);_9W=_9Y;continue;case 1:var _a3=E(_9u)(_9T,_a1[1],_a0);_9W=_9Y;continue;default:var _a4=E(_9t)(_9T,_a1[1],_a0);_9W=_9Y;continue;}}else{var _a5=B(_9B(_9Z[1],_));_9W=_9Y;continue;}}}break;case 1:var _a6=E(_9A),_a7=E(_9u),_a8=_a7(_a6,_9S[1],_9R),_a9=_9P;while(1){var _aa=E(_a9);if(!_aa[0]){return _a;}else{var _ab=_aa[2],_ac=E(_aa[1]);if(!_ac[0]){var _ad=_ac[2],_ae=E(_ac[1]);switch(_ae[0]){case 0:var _af=E(_1)(_a6,_ae[1],_ad);_a9=_ab;continue;case 1:var _ag=_a7(_a6,_ae[1],_ad);_a9=_ab;continue;default:var _ah=E(_9t)(_a6,_ae[1],_ad);_a9=_ab;continue;}}else{var _ai=B(_9B(_ac[1],_));_a9=_ab;continue;}}}break;default:var _aj=E(_9A),_ak=E(_9t),_al=_ak(_aj,_9S[1],_9R),_am=_9P;while(1){var _an=E(_am);if(!_an[0]){return _a;}else{var _ao=_an[2],_ap=E(_an[1]);if(!_ap[0]){var _aq=_ap[2],_ar=E(_ap[1]);switch(_ar[0]){case 0:var _as=E(_1)(_aj,_ar[1],_aq);_am=_ao;continue;case 1:var _at=E(_9u)(_aj,_ar[1],_aq);_am=_ao;continue;default:var _au=_ak(_aj,_ar[1],_aq);_am=_ao;continue;}}else{var _av=B(_9B(_ap[1],_));_am=_ao;continue;}}}}}else{var _aw=B(_9B(_9Q[1],_));_9L=_9P;return null;}}})(_9L,_));if(_9M!=null){return _9M;}}};return new F(function(){return A(_2,[_9x,function(_){return new F(function(){return _9K(_9z,_);});}]);});},_ax=function(_ay,_az,_aA,_aB){var _aC=B(_9i(_az)),_aD=function(_aE){return new F(function(){return A(_9k,[_aC,new T(function(){return B(_9v(_ay,_az,_aE,_aB));}),new T(function(){return B(A(_9o,[_aC,_aE]));})]);});};return new F(function(){return A(_9m,[_aC,_aA,_aD]);});},_aF=function(_aG,_){var _aH=E(_aG);if(!_aH[0]){return _3n;}else{var _aI=B(A(_ax,[_S,_6B,_9h,[1,[1,[1,_aH[1],_3n]],_3n],_])),_aJ=B(_aF(_aH[2],_));return [1,_aI,_aJ];}},_aK=function(_aL,_aM,_){var _aN=B(A(_ax,[_S,_6B,_9h,[1,[1,[1,_aL,_3n]],_3n],_])),_aO=B(_aF(_aM,_));return [1,_aN,_aO];},_aP=(function(s){return document.createTextNode(s);}),_aQ=function(_aR,_){var _aS=jsShow(_aR),_aT=E(_aP)(toJSStr(fromJSStr(_aS)));return new F(function(){return A(_ax,[_S,_6B,_9h,[1,[1,[1,_aT,_3n]],_3n],_]);});},_aU=function(_aV,_aW){var _aX=(_aW-_aV)*25/900;if(!_aX){var _aY=rintDouble(0);return _aY&4294967295;}else{if(_aX<=0){var _aZ=rintDouble( -_aX/0.1);return _aZ&4294967295;}else{var _b0=rintDouble(_aX/0.1);return _b0&4294967295;}}},_b1=function(_b2,_b3){return [0,E(_b2),toJSStr(E(_b3))];},_b4=2,_b5=0,_b6=new T(function(){return B(unCStr("x1"));}),_b7=new T(function(){return B(unCStr("y1"));}),_b8=new T(function(){return B(unCStr("x2"));}),_b9=new T(function(){return B(unCStr("y2"));}),_ba=new T(function(){return B(unCStr("frames"));}),_bb=new T(function(){return B(unCStr("time (minutes)"));}),_bc=new T(function(){return B(unCStr("title"));}),_bd=new T(function(){return B(unCStr("Delete"));}),_be=[1,_bd,_3n],_bf=[1,_bc,_be],_bg=[1,_bb,_bf],_bh=[1,_ba,_bg],_bi=[1,_b9,_bh],_bj=[1,_b8,_bi],_bk=function(_){return new F(function(){return E(_4)("span");});},_bl=new T(function(){return [0,[2,"class"],"glyphicon glyphicon-remove"];}),_bm=[1,_bl,_3n],_bn=new T(function(){return B(_ax(_S,_6B,_bk,_bm));}),_bo=function(_){return new F(function(){return E(_4)("input");});},_bp=function(_){return new F(function(){return E(_4)("tr");});},_bq=function(_){return new F(function(){return E(_4)("th");});},_br=function(_){return new F(function(){return E(_4)("button");});},_bs=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_bt=function(_bu){var _bv=I_decodeDouble(_bu);return [0,[1,_bv[2]],_bv[1]];},_bw=function(_bx){var _by=E(_bx);if(!_by[0]){return _by[1];}else{return new F(function(){return I_toNumber(_by[1]);});}},_bz=function(_bA){return [0,_bA];},_bB=function(_bC){var _bD=hs_intToInt64(2147483647),_bE=hs_leInt64(_bC,_bD);if(!_bE){return [1,I_fromInt64(_bC)];}else{var _bF=hs_intToInt64(-2147483648),_bG=hs_geInt64(_bC,_bF);if(!_bG){return [1,I_fromInt64(_bC)];}else{var _bH=hs_int64ToInt(_bC);return new F(function(){return _bz(_bH);});}}},_bI=function(_bJ){var _bK=hs_intToInt64(_bJ);return E(_bK);},_bL=function(_bM){var _bN=E(_bM);if(!_bN[0]){return new F(function(){return _bI(_bN[1]);});}else{return new F(function(){return I_toInt64(_bN[1]);});}},_bO=new T(function(){return [2,"value"];}),_bP=new T(function(){return [0,[2,"type"],"text"];}),_bQ=new T(function(){return [0,[2,"class"],"btn btn-danger"];}),_bR=function(_bS){return E(E(_bS)[1]);},_bT=function(_bU){return E(E(_bU)[2]);},_bV=function(_bW){return E(E(_bW)[1]);},_bX=function(_){return new F(function(){return nMV(_6t);});},_bY=new T(function(){return B(_8L(_bX));}),_bZ=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_c0=function(_c1){return E(E(_c1)[2]);},_c2=function(_c3,_c4,_c5,_c6,_c7,_c8){var _c9=B(_bR(_c3)),_ca=B(_9i(_c9)),_cb=new T(function(){return B(_2(_c9));}),_cc=new T(function(){return B(_9o(_ca));}),_cd=new T(function(){return B(A(_9r,[_c4,_c6]));}),_ce=new T(function(){return B(A(_bV,[_c5,_c7]));}),_cf=function(_cg){return new F(function(){return A(_cc,[[0,_ce,_cd,_cg]]);});},_ch=function(_ci){var _cj=new T(function(){var _ck=new T(function(){var _cl=__createJSFunc(2,function(_cm,_){var _cn=B(A(E(_ci),[_cm,_]));return _8P;}),_co=_cl;return function(_){return new F(function(){return E(_bZ)(E(_cd),E(_ce),_co);});};});return B(A(_cb,[_ck]));});return new F(function(){return A(_9m,[_ca,_cj,_cf]);});},_cp=new T(function(){var _cq=new T(function(){return B(_2(_c9));}),_cr=function(_cs){var _ct=new T(function(){return B(A(_cq,[function(_){var _=wMV(E(_bY),[1,_cs]);return new F(function(){return A(_bT,[_c5,_c7,_cs,_]);});}]));});return new F(function(){return A(_9m,[_ca,_ct,_c8]);});};return B(A(_c0,[_c3,_cr]));});return new F(function(){return A(_9m,[_ca,_cp,_ch]);});},_cu=function(_cv,_cw){while(1){var _cx=E(_cv);if(!_cx[0]){return E(_cw);}else{var _cy=[1,_cx[1],_cw];_cv=_cx[2];_cw=_cy;continue;}}},_cz=function(_cA,_cB){while(1){var _cC=E(_cA);if(!_cC[0]){_cA=[1,I_fromInt(_cC[1])];continue;}else{return [1,I_shiftLeft(_cC[1],_cB)];}}},_cD=function(_cE,_cF,_cG,_cH,_){var _cI=E(_bs)(_cH),_cJ=E(_aP),_cK=_cJ(toJSStr(E(_b6))),_cL=B(A(_ax,[_S,_6B,_bq,[1,[1,[1,_cK,_3n]],_3n],_])),_cM=function(_cN,_){var _cO=E(_cN);if(!_cO[0]){return _3n;}else{var _cP=_cJ(toJSStr(E(_cO[1]))),_cQ=B(A(_ax,[_S,_6B,_bq,[1,[1,[1,_cP,_3n]],_3n],_])),_cR=B(_cM(_cO[2],_));return [1,_cQ,_cR];}},_cS=B((function(_cT,_cU,_){var _cV=_cJ(toJSStr(E(_cT))),_cW=B(A(_ax,[_S,_6B,_bq,[1,[1,[1,_cV,_3n]],_3n],_])),_cX=B(_cM(_cU,_));return [1,_cW,_cX];})(_b7,_bj,_)),_cY=B(A(_ax,[_S,_6B,_bp,[1,[1,[1,_cL,_cS]],_3n],_])),_cZ=E(_9q),_d0=_cZ(E(_cY),_cH),_d1=function(_d2,_){var _d3=E(_d2);if(!_d3[0]){return _3n;}else{var _d4=E(_d3[1]),_d5=E(_d4[1]),_d6=E(_d4[2]),_d7=E(_d5[1]),_d8=B(_aQ(_d7*25/900,_)),_d9=_d8,_da=E(_d5[2]),_db=B(_aQ(_da*25/900,_)),_dc=_db,_dd=E(_d6[1]),_de=B(_aQ(_dd*25/900,_)),_df=_de,_dg=E(_d6[2]),_dh=B(_aQ(_dg*25/900,_)),_di=_dh,_dj=function(_dk){var _dl=B(_aQ(_dk,_)),_dm=_dl,_dn=function(_do){var _dp=rintDouble(_do*5.8333333333333334e-2),_dq=B(_bt(_dp)),_dr=_dq[1],_ds=_dq[2],_dt=function(_du){var _dv=B(_aQ(_du,_)),_dw=B(_aK(_d9,[1,_dc,[1,_df,[1,_di,[1,_dm,[1,_dv,_3n]]]]],_)),_dx=B(A(_ax,[_S,_6B,_bp,[1,new T(function(){return B(_7J(_dw));}),_3n],_])),_dy=B(A(_ax,[_S,_6B,_bo,[1,_bP,[1,new T(function(){return B(_b1(_bO,_d4[3]));}),_3n]],_])),_dz=B(A(_bn,[_])),_dA=B(A(_ax,[_S,_6B,_br,[1,_bQ,[1,[1,[1,_dz,_3n]],_3n]],_])),_dB=B(A(_ax,[_S,_6B,_9h,[1,[1,[1,_dy,_3n]],_3n],_])),_dC=E(_dx),_dD=_cZ(E(_dB),_dC),_dE=E(_dA),_dF=_cZ(_dE,_dC),_dG=new T(function(){return B(A(_cF,[_d4]));}),_dH=B(A(_c2,[_6C,_S,_9g,_dE,_b5,function(_dI){return E(_dG);},_])),_dJ=new T(function(){return B(A(_cE,[_dy,_d4]));}),_dK=B(A(_c2,[_6C,_S,_o,_dy,_b4,function(_dL){return E(_dJ);},_])),_dM=_cZ(_dC,_cH),_dN=B(_d1(_d3[2],_));return [1,_a,_dN];};if(_ds>=0){return new F(function(){return _dt(B(_bw(B(_cz(_dr,_ds)))));});}else{var _dO=hs_uncheckedIShiftRA64(B(_bL(_dr)), -_ds);return new F(function(){return _dt(B(_bw(B(_bB(_dO)))));});}};if(_d7!=_dd){return new F(function(){return _dn(B(_aU(_d7,_dd)));});}else{return new F(function(){return _dn(B(_aU(_da,_dg)));});}};if(_d7!=_dd){return new F(function(){return _dj(B(_aU(_d7,_dd)));});}else{return new F(function(){return _dj(B(_aU(_da,_dg)));});}}},_dP=B(_d1(B(_cu(E(_cG)[2],_3n)),_));return _a;},_dQ=function(_){return _a;},_dR=(function(ctx){ctx.restore();}),_dS=(function(ctx){ctx.save();}),_dT=(function(ctx,x,y){ctx.scale(x,y);}),_dU=function(_dV,_dW,_dX,_dY,_){var _dZ=E(_dS)(_dY),_e0=E(_dT)(_dY,E(_dV),E(_dW)),_e1=B(A(_dX,[_dY,_])),_e2=E(_dR)(_dY);return new F(function(){return _dQ(_);});},_e3=(function(ctx){ctx.beginPath();}),_e4=(function(ctx){ctx.stroke();}),_e5=function(_e6,_e7,_){var _e8=E(_e3)(_e7),_e9=B(A(_e6,[_e7,_])),_ea=E(_e4)(_e7);return new F(function(){return _dQ(_);});},_eb=(function(ctx,i,x,y){ctx.drawImage(i,x,y);}),_ec=function(_ed,_ee,_ef,_eg,_){var _eh=E(_eb)(_eg,_ed,_ee,_ef);return new F(function(){return _dQ(_);});},_ei=",",_ej="[",_ek="]",_el="{",_em="}",_en=":",_eo="\"",_ep="true",_eq="false",_er="null",_es=new T(function(){return JSON.stringify;}),_et=function(_eu,_ev){var _ew=E(_ev);switch(_ew[0]){case 0:return [0,new T(function(){return jsShow(_ew[1]);}),_eu];case 1:return [0,new T(function(){var _ex=E(_es)(_ew[1]);return String(_ex);}),_eu];case 2:return (!E(_ew[1]))?[0,_eq,_eu]:[0,_ep,_eu];case 3:var _ey=E(_ew[1]);if(!_ey[0]){return [0,_ej,[1,_ek,_eu]];}else{var _ez=new T(function(){var _eA=new T(function(){var _eB=function(_eC){var _eD=E(_eC);if(!_eD[0]){return [1,_ek,_eu];}else{var _eE=new T(function(){var _eF=B(_et(new T(function(){return B(_eB(_eD[2]));}),_eD[1]));return [1,_eF[1],_eF[2]];});return [1,_ei,_eE];}};return B(_eB(_ey[2]));}),_eG=B(_et(_eA,_ey[1]));return [1,_eG[1],_eG[2]];});return [0,_ej,_ez];}break;case 4:var _eH=E(_ew[1]);if(!_eH[0]){return [0,_el,[1,_em,_eu]];}else{var _eI=E(_eH[1]),_eJ=new T(function(){var _eK=new T(function(){var _eL=function(_eM){var _eN=E(_eM);if(!_eN[0]){return [1,_em,_eu];}else{var _eO=E(_eN[1]),_eP=new T(function(){var _eQ=B(_et(new T(function(){return B(_eL(_eN[2]));}),_eO[2]));return [1,_eQ[1],_eQ[2]];});return [1,_ei,[1,_eo,[1,_eO[1],[1,_eo,[1,_en,_eP]]]]];}};return B(_eL(_eH[2]));}),_eR=B(_et(_eK,_eI[2]));return [1,_eR[1],_eR[2]];});return [0,_el,[1,new T(function(){var _eS=E(_es)(E(_eI[1]));return String(_eS);}),[1,_en,_eJ]]];}break;default:return [0,_er,_eu];}},_eT=new T(function(){return toJSStr(_3n);}),_eU=function(_eV){var _eW=B(_et(_3n,_eV)),_eX=jsCat([1,_eW[1],_eW[2]],E(_eT));return E(_eX);},_eY=function(_eZ,_f0){return E(_eZ)!=E(_f0);},_f1=function(_f2,_f3){return E(_f2)==E(_f3);},_f4=[0,_f1,_eY],_f5=function(_f6,_f7,_f8){while(1){var _f9=E(_f8);if(!_f9[0]){return false;}else{if(!B(A(_T,[_f6,_f7,_f9[1]]))){_f8=_f9[2];continue;}else{return true;}}}},_fa=32,_fb=function(_fc){while(1){var _fd=E(_fc);if(!_fd[0]){return false;}else{var _fe=E(_fd[1]);if(!_fe[0]){return true;}else{if(!B(_f5(_f4,_fa,_fe))){_fc=_fd[2];continue;}else{return true;}}}}},_ff=function(_fg){return E(E(_fg)[3]);},_fh=function(_fi,_fj,_fk){var _fl=E(_fi);return (_fl[0]==0)?false:(!B(_fb(B(_1A(_ff,_fl)))))?(!B(_26(_fj,_3n)))?(!B(_f5(_f4,_fa,_fj)))?(E(_fk)[0]==0)?false:true:false:false:false;},_fm=(function(id){return document.getElementById(id);}),_fn=function(_fo,_fp){var _fq=function(_){var _fr=E(_fm)(E(_fp)),_fs=__eq(_fr,E(_8P));return (E(_fs)==0)?[1,_fr]:_6t;};return new F(function(){return A(_2,[_fo,_fq]);});},_ft=new T(function(){return encodeURIComponent;}),_fu=new T(function(){return B(unCStr("data:text/plain;charset=utf-8,"));}),_fv=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:190:3-9"));}),_fw=[0,_6t,_6u,_3n,_fv,_6t,_6t],_fx=new T(function(){return B(_6r(_fw));}),_fy=new T(function(){return B(unCStr("href"));}),_fz=function(_fA){return new F(function(){return toJSStr(E(_fA));});},_fB=function(_fC,_fD,_){var _fE=B(A(_fn,[_6B,new T(function(){return B(_fz(_fC));},1),_])),_fF=E(_fE);if(!_fF[0]){return new F(function(){return die(_fx);});}else{var _fG=E(_ft)(toJSStr(_fD)),_fH=E(_9t)(E(_fF[1]),toJSStr(E(_fy)),toJSStr(B(_16(_fu,new T(function(){var _fI=String(_fG);return fromJSStr(_fI);},1)))));return new F(function(){return _dQ(_);});}},_fJ=(function(ctx,rad){ctx.rotate(rad);}),_fK=function(_fL,_fM,_fN,_){var _fO=E(_dS)(_fN),_fP=E(_fJ)(_fN,E(_fL)),_fQ=B(A(_fM,[_fN,_])),_fR=E(_dR)(_fN);return new F(function(){return _dQ(_);});},_fS=(function(ctx,x,y){ctx.translate(x,y);}),_fT=function(_fU,_fV,_fW,_fX,_){var _fY=E(_dS)(_fX),_fZ=E(_fS)(_fX,E(_fU),E(_fV)),_g0=B(A(_fW,[_fX,_])),_g1=E(_dR)(_fX);return new F(function(){return _dQ(_);});},_g2=function(_g3,_g4){if(_g4<=0){var _g5=function(_g6){var _g7=function(_g8){var _g9=function(_ga){var _gb=function(_gc){var _gd=isDoubleNegativeZero(_g4),_ge=_gd,_gf=function(_gg){var _gh=E(_g3);if(!_gh){return (_g4>=0)?(E(_ge)==0)?E(_g4):3.141592653589793:3.141592653589793;}else{var _gi=E(_g4);return (_gi==0)?E(_gh):_gi+_gh;}};if(!E(_ge)){return new F(function(){return _gf(_);});}else{var _gj=E(_g3),_gk=isDoubleNegativeZero(_gj);if(!E(_gk)){return new F(function(){return _gf(_);});}else{return  -B(_g2( -_gj,_g4));}}};if(_g4>=0){return new F(function(){return _gb(_);});}else{var _gl=E(_g3),_gm=isDoubleNegativeZero(_gl);if(!E(_gm)){return new F(function(){return _gb(_);});}else{return  -B(_g2( -_gl,_g4));}}};if(_g4>0){return new F(function(){return _g9(_);});}else{var _gn=E(_g3);if(_gn>=0){return new F(function(){return _g9(_);});}else{return  -B(_g2( -_gn,_g4));}}};if(_g4>=0){return new F(function(){return _g7(_);});}else{var _go=E(_g3);if(_go<=0){return new F(function(){return _g7(_);});}else{return 3.141592653589793+Math.atan(_go/_g4);}}};if(!E(_g4)){if(E(_g3)<=0){return new F(function(){return _g5(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _g5(_);});}}else{return new F(function(){return Math.atan(E(_g3)/_g4);});}},_gp=function(_gq,_gr){return E(_gq)-E(_gr);},_gs=function(_gt,_gu,_gv,_gw,_gx,_gy,_gz,_gA){return new F(function(){return Math.atan((Math.tan(B(_g2(new T(function(){return B(_gp(_gw,_gu));}),_gv-_gt))-1.5707963267948966)+Math.tan(B(_g2(new T(function(){return B(_gp(_gy,_gw));}),_gx-_gv)))+Math.tan(B(_g2(new T(function(){return B(_gp(_gA,_gy));}),_gz-_gx))+1.5707963267948966)+Math.tan(B(_g2(new T(function(){return B(_gp(_gu,_gA));}),_gt-_gz))-3.141592653589793))/4);});},_gB=function(_gC){return E(_gC)/2;},_gD=function(_gE,_gF,_gG,_){var _gH=E(_gE);return new F(function(){return _fT(_gH[1],_gH[2],_gF,E(_gG),_);});},_gI=function(_gJ,_gK){var _gL=new T(function(){var _gM=E(_gJ),_gN=E(E(_gK)[2]),_gO=E(_gN[1]),_gP=E(_gO[1]),_gQ=E(_gO[2]),_gR=E(_gN[2]),_gS=E(_gR[1]),_gT=E(_gR[2]),_gU=E(_gN[3]),_gV=E(_gU[1]),_gW=E(_gU[2]),_gX=E(_gN[4]),_gY=E(_gX[1]),_gZ=E(_gX[2]);return Math.sqrt(E(_gM[1])*E(_gM[2])/(0.5*(_gP*_gZ+_gY*_gW+_gV*_gQ-_gP*_gW-_gV*_gZ-_gY*_gQ)+0.5*(_gY*_gW+_gV*_gT+_gS*_gZ-_gY*_gT-_gS*_gW-_gV*_gZ)));}),_h0=new T(function(){var _h1=E(_gJ);return [0,new T(function(){return B(_gB(_h1[1]));}),new T(function(){return B(_gB(_h1[2]));})];}),_h2=new T(function(){var _h3=E(E(_gK)[2]),_h4=E(_h3[1]),_h5=E(_h3[2]),_h6=E(_h3[3]),_h7=E(_h3[4]);return  -B(_gs(E(_h4[1]),_h4[2],E(_h5[1]),_h5[2],E(_h6[1]),_h6[2],E(_h7[1]),_h7[2]));}),_h8=new T(function(){var _h9=E(E(_gK)[2]),_ha=E(_h9[1]),_hb=E(_h9[2]),_hc=E(_h9[3]),_hd=E(_h9[4]);return [0,new T(function(){return (E(_ha[1])+E(_hb[1])+E(_hc[1])+E(_hd[1]))/4/(-1);}),new T(function(){return (E(_ha[2])+E(_hb[2])+E(_hc[2])+E(_hd[2]))/4/(-1);})];}),_he=function(_hf,_hg,_){var _hh=E(_h0),_hi=function(_hj,_){var _hk=function(_hl,_){return new F(function(){return _fK(_h2,function(_hm,_){return new F(function(){return _gD(_h8,_hf,_hm,_);});},E(_hl),_);});};return new F(function(){return _dU(_gL,_gL,_hk,E(_hj),_);});};return new F(function(){return _fT(_hh[1],_hh[2],_hi,E(_hg),_);});};return E(_he);},_hn=(function(ctx,x,y){ctx.moveTo(x,y);}),_ho=(function(ctx,x,y){ctx.lineTo(x,y);}),_hp=function(_hq,_hr,_){var _hs=E(_hq);if(!_hs[0]){return _a;}else{var _ht=E(_hs[1]),_hu=E(_hr),_hv=E(_hn)(_hu,E(_ht[1]),E(_ht[2])),_hw=E(_hs[2]);if(!_hw[0]){return _a;}else{var _hx=E(_hw[1]),_hy=E(_ho),_hz=_hy(_hu,E(_hx[1]),E(_hx[2])),_hA=_hw[2];while(1){var _hB=E(_hA);if(!_hB[0]){return _a;}else{var _hC=E(_hB[1]),_hD=_hy(_hu,E(_hC[1]),E(_hC[2]));_hA=_hB[2];continue;}}}}},_hE=function(_hF,_hG,_){var _hH=new T(function(){return E(E(_hF)[2]);}),_hI=new T(function(){return E(E(_hH)[1]);});return new F(function(){return _hp([1,_hI,[1,new T(function(){return E(E(_hH)[2]);}),[1,new T(function(){return E(E(_hH)[3]);}),[1,new T(function(){return E(E(_hH)[4]);}),[1,_hI,_3n]]]]],_hG,_);});},_hJ=(function(e){e.width = e.width;}),_hK=",",_hL="rgba(",_hM=new T(function(){return toJSStr(_3n);}),_hN="rgb(",_hO=")",_hP=[1,_hO,_3n],_hQ=function(_hR){var _hS=E(_hR);if(!_hS[0]){var _hT=jsCat([1,_hN,[1,new T(function(){return String(_hS[1]);}),[1,_hK,[1,new T(function(){return String(_hS[2]);}),[1,_hK,[1,new T(function(){return String(_hS[3]);}),_hP]]]]]],E(_hM));return E(_hT);}else{var _hU=jsCat([1,_hL,[1,new T(function(){return String(_hS[1]);}),[1,_hK,[1,new T(function(){return String(_hS[2]);}),[1,_hK,[1,new T(function(){return String(_hS[3]);}),[1,_hK,[1,new T(function(){return String(_hS[4]);}),_hP]]]]]]]],E(_hM));return E(_hU);}},_hV="strokeStyle",_hW="fillStyle",_hX=(function(e,p){return e[p].toString();}),_hY=function(_hZ,_i0){var _i1=new T(function(){return B(_hQ(_hZ));});return function(_i2,_){var _i3=E(_i2),_i4=E(_hW),_i5=E(_hX),_i6=_i5(_i3,_i4),_i7=E(_hV),_i8=_i5(_i3,_i7),_i9=E(_i1),_ia=E(_1),_ib=_ia(_i3,_i4,_i9),_ic=_ia(_i3,_i7,_i9),_id=B(A(_i0,[_i3,_])),_ie=String(_i6),_if=_ia(_i3,_i4,_ie),_ig=String(_i8),_ih=_ia(_i3,_i7,_ig);return new F(function(){return _dQ(_);});};},_ii=function(_ij,_ik,_il){var _im=E(_il);if(!_im[0]){return [0];}else{var _in=_im[1],_io=_im[2];return (!B(A(_ij,[_ik,_in])))?[1,_in,new T(function(){return B(_ii(_ij,_ik,_io));})]:E(_io);}},_ip="lineWidth",_iq=function(_ir,_is){var _it=new T(function(){return String(E(_ir));});return function(_iu,_){var _iv=E(_iu),_iw=E(_ip),_ix=E(_hX)(_iv,_iw),_iy=E(_1),_iz=_iy(_iv,_iw,E(_it)),_iA=B(A(_is,[_iv,_])),_iB=String(_ix),_iC=_iy(_iv,_iw,_iB);return new F(function(){return _dQ(_);});};},_iD=new T(function(){return B(unCStr("saveLink"));}),_iE=new T(function(){return B(unCStr("exportLink"));}),_iF=[0,255,0,255],_iG=1,_iH=0.2,_iI=900,_iJ=[0,_iI,_iI],_iK=new T(function(){return B(unCStr("btn btn-primary"));}),_iL=new T(function(){return B(unCStr("class"));}),_iM=new T(function(){return B(unCStr("btn btn-primary disabled"));}),_iN="exportLink",_iO=new T(function(){return B(_fn(_6B,_iN));}),_iP=new T(function(){return B(unCStr("value"));}),_iQ="runfile",_iR=new T(function(){return B(_fn(_6B,_iQ));}),_iS="scans",_iT=new T(function(){return B(_fn(_6B,_iS));}),_iU=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:168:3-8"));}),_iV=[0,_6t,_6u,_3n,_iU,_6t,_6t],_iW=new T(function(){return B(_6r(_iV));}),_iX=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:150:3-14"));}),_iY=[0,_6t,_6u,_3n,_iX,_6t,_6t],_iZ=new T(function(){return B(_6r(_iY));}),_j0=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:149:3-10"));}),_j1=[0,_6t,_6u,_3n,_j0,_6t,_6t],_j2=new T(function(){return B(_6r(_j1));}),_j3=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:148:3-11"));}),_j4=[0,_6t,_6u,_3n,_j3,_6t,_6t],_j5=new T(function(){return B(_6r(_j4));}),_j6="aligned",_j7=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:147:3-11"));}),_j8=[0,_6t,_6u,_3n,_j7,_6t,_6t],_j9=new T(function(){return B(_6r(_j8));}),_ja="original",_jb=function(_jc,_jd,_){while(1){var _je=E(_jc);if(!_je[0]){return _a;}else{var _jf=E(_je[1]),_jg=B(_hp([1,_jf[1],[1,_jf[2],_3n]],_jd,_));_jc=_je[2];continue;}}},_jh=[0,255,0,255],_ji=1,_jj=function(_jk){var _jl=new T(function(){var _jm=function(_jn,_jo){return new F(function(){return _jb(E(_jk)[2],_jn,_jo);});};return B(_hY(_jh,function(_jp,_){return new F(function(){return _e5(_jm,E(_jp),_);});}));});return new F(function(){return _iq(_ji,_jl);});},_jq=function(_jr){while(1){var _js=E(_jr);if(!_js[0]){_jr=[1,I_fromInt(_js[1])];continue;}else{return new F(function(){return I_toString(_js[1]);});}}},_jt=function(_ju,_jv){return new F(function(){return _16(fromJSStr(B(_jq(_ju))),_jv);});},_jw=function(_jx,_jy){var _jz=E(_jx);if(!_jz[0]){var _jA=_jz[1],_jB=E(_jy);return (_jB[0]==0)?_jA<_jB[1]:I_compareInt(_jB[1],_jA)>0;}else{var _jC=_jz[1],_jD=E(_jy);return (_jD[0]==0)?I_compareInt(_jC,_jD[1])<0:I_compare(_jC,_jD[1])<0;}},_jE=[0,0],_jF=function(_jG,_jH,_jI){if(_jG<=6){return new F(function(){return _jt(_jH,_jI);});}else{if(!B(_jw(_jH,_jE))){return new F(function(){return _jt(_jH,_jI);});}else{return [1,_7T,new T(function(){return B(_16(fromJSStr(B(_jq(_jH))),[1,_7S,_jI]));})];}}},_jJ=0,_jK=1,_jL=function(_jM){var _jN=E(_jM);if(!_jN[0]){return [0];}else{return new F(function(){return _16(_jN[1],new T(function(){return B(_jL(_jN[2]));},1));});}},_jO=new T(function(){return B(unCStr("\r\n"));}),_jP=new T(function(){return B(_16(_jO,_jO));}),_jQ=function(_jR,_jS){var _jT=E(_jS);return (_jT[0]==0)?[0]:[1,_jR,[1,_jT[1],new T(function(){return B(_jQ(_jR,_jT[2]));})]];},_jU=new T(function(){return B(unCStr("  ccdacq"));}),_jV=new T(function(){return B(unAppCStr("}",_jO));}),_jW=new T(function(){return B(_16(_jO,_jV));}),_jX=new T(function(){return B(_7U(0,1,_3n));}),_jY=new T(function(){return B(unCStr("1"));}),_jZ=new T(function(){return B(_16(_jY,_3n));}),_k0=[1,_fa,_jZ],_k1=new T(function(){return B(_16(_jX,_k0));}),_k2=[1,_fa,_k1],_k3=new T(function(){var _k4=jsShow(0);return fromJSStr(_k4);}),_k5=new T(function(){var _k6=jsShow(0.1);return fromJSStr(_k6);}),_k7=new T(function(){return B(unCStr("ccdtrans sav"));}),_k8=function(_k9,_ka,_kb,_kc){if(!E(_k9)){var _kd=new T(function(){var _ke=E(_kb),_kf=E(_ke[1]),_kg=_kf[2],_kh=E(_ka),_ki=function(_kj){var _kk=jsShow(_kj),_kl=new T(function(){var _km=new T(function(){var _kn=new T(function(){var _ko=E(_kf[1]),_kp=E(_ke[2]),_kq=E(_kp[1]),_kr=function(_ks){var _kt=new T(function(){var _ku=new T(function(){var _kv=new T(function(){var _kw=new T(function(){var _kx=new T(function(){var _ky=new T(function(){var _kz=E(_kh[6]),_kA=E(_kc),_kB=_kz+12.5+(_ko*25/900-12.5)*Math.cos(_kA),_kC=jsShow(_kB),_kD=new T(function(){var _kE=new T(function(){var _kF=jsShow((_kz+12.5+(_kq*25/900-12.5)*Math.cos(_kA)-_kB)/_ks),_kG=new T(function(){var _kH=new T(function(){var _kI=(_ko*25/900-12.5)*Math.sin(_kA),_kJ=jsShow(_kI),_kK=new T(function(){var _kL=new T(function(){var _kM=jsShow(((_kq*25/900-12.5)*Math.sin(_kA)-_kI)/_ks),_kN=new T(function(){var _kO=new T(function(){var _kP=new T(function(){var _kQ=new T(function(){return B(_16(_k5,[1,_fa,new T(function(){return B(_16(_ke[3],_3n));})]));});return B(_16(B(_16(_jU,[1,_fa,_kQ])),_jW));},1);return B(_16(_jO,_kP));});return B(unAppCStr(")",_kO));},1);return B(_16(fromJSStr(_kM),_kN));});return B(unAppCStr("+i*",_kL));},1);return B(_16(fromJSStr(_kJ),_kK));});return B(unAppCStr(") tmp2 (",_kH));},1);return B(_16(fromJSStr(_kF),_kG));});return B(unAppCStr("+i*",_kE));},1);return B(_16(fromJSStr(_kC),_kD));});return B(unAppCStr("  umv sah (",_ky));},1);return B(_16(_jO,_kx));});return B(unAppCStr("{",_kw));},1);return B(_16(_jO,_kv));});return B(unAppCStr(";i+=1)",_ku));},1);return new F(function(){return _16(B(_7U(0,_ks,_3n)),_kt);});};if(_ko!=_kq){return B(_kr(B(_aU(_ko,_kq))));}else{return B(_kr(B(_aU(E(_kg),E(_kp[2])))));}});return B(unAppCStr("for(i=0;i<=",_kn));},1);return B(_16(_jO,_km));},1);return new F(function(){return _16(fromJSStr(_kk),_kl);});};if(!E(_kh[7])){return B(_ki(E(_kh[4])+E(_kg)*25/900));}else{return B(_ki(E(_kh[5])+E(_kg)*25/900));}});return new F(function(){return unAppCStr("umv sav ",_kd);});}else{var _kR=new T(function(){var _kS=E(_kb),_kT=E(_kS[1]),_kU=_kT[2],_kV=E(_ka),_kW=_kV[4],_kX=_kV[5],_kY=_kV[7],_kZ=E(_kT[1]),_l0=E(_kc),_l1=jsShow(E(_kV[6])+12.5+(_kZ*25/900-12.5)*Math.cos(_l0)),_l2=new T(function(){var _l3=new T(function(){var _l4=jsShow((_kZ*25/900-12.5)*Math.sin(_l0)),_l5=new T(function(){var _l6=new T(function(){var _l7=new T(function(){var _l8=new T(function(){var _l9=E(_kS[2]),_la=_l9[2],_lb=new T(function(){var _lc=new T(function(){var _ld=E(_l9[1]),_le=function(_lf){var _lg=new T(function(){return B(_16(_k3,[1,_fa,new T(function(){return B(_16(_kS[3],_k2));})]));});return new F(function(){return _16(B(_7U(0,_lf,_3n)),[1,_fa,_lg]);});};if(_kZ!=_ld){return B(_le(B(_aU(_kZ,_ld))));}else{return B(_le(B(_aU(E(_kU),E(_la)))));}});return B(_16(_k5,[1,_fa,_lc]));});if(!E(_kY)){var _lh=jsShow(E(_kW)+E(_la)*25/900);return B(_16(fromJSStr(_lh),[1,_fa,_lb]));}else{var _li=jsShow(E(_kX)+E(_la)*25/900);return B(_16(fromJSStr(_li),[1,_fa,_lb]));}});if(!E(_kY)){var _lj=jsShow(E(_kW)+E(_kU)*25/900);return B(_16(fromJSStr(_lj),[1,_fa,_l8]));}else{var _lk=jsShow(E(_kX)+E(_kU)*25/900);return B(_16(fromJSStr(_lk),[1,_fa,_l8]));}});return B(_16(_k7,[1,_fa,_l7]));},1);return B(_16(_jO,_l6));},1);return B(_16(fromJSStr(_l4),_l5));});return B(unAppCStr(" tmp2 ",_l3));},1);return B(_16(fromJSStr(_l1),_l2));});return new F(function(){return unAppCStr("umv sah ",_kR);});}},_ll=function(_lm){var _ln=new T(function(){var _lo=E(_lm),_lp=new T(function(){var _lq=new T(function(){var _lr=function(_ls){var _lt=new T(function(){var _lu=E(_ls),_lv=rintDouble(_lu*180/3.141592653589793),_lw=B(_bt(_lv)),_lx=_lw[1],_ly=_lw[2],_lz=new T(function(){var _lA=new T(function(){var _lB=B(_1A(function(_lC){var _lD=E(_lC);if(E(E(_lD[1])[1])!=E(E(_lD[2])[1])){return new F(function(){return _k8(_jJ,_lo,_lD,_lu);});}else{return new F(function(){return _k8(_jK,_lo,_lD,_lu);});}},B(_cu(_lo[2],_3n))));if(!_lB[0]){return [0];}else{return B(_jL([1,_lB[1],new T(function(){return B(_jQ(_jO,_lB[2]));})]));}},1);return B(_16(_jO,_lA));});if(_ly>=0){return B(_16(B(_jF(0,B(_cz(_lx,_ly)),_3n)),_lz));}else{var _lE=hs_uncheckedIShiftRA64(B(_bL(_lx)), -_ly);return B(_16(B(_jF(0,B(_bB(_lE)),_3n)),_lz));}});return new F(function(){return unAppCStr("umv sar ",_lt);});},_lF=B(_1A(_lr,_lo[8]));if(!_lF[0]){return [0];}else{return B(_jL([1,_lF[1],new T(function(){return B(_jQ(_jP,_lF[2]));})]));}},1);return B(_16(_jO,_lq));},1);return B(_16(_lo[3],_lp));});return new F(function(){return unAppCStr("ccdnewfile ",_ln);});},_lG=function(_lH){return new F(function(){return fromJSStr(E(_lH));});},_lI=function(_lJ,_lK,_lL,_lM){var _lN=new T(function(){var _lO=function(_){var _lP=E(_hX)(B(A(_9r,[_lJ,_lL])),E(_lM));return new T(function(){return String(_lP);});};return E(_lO);});return new F(function(){return A(_2,[_lK,_lN]);});},_lQ=function(_lR,_lS,_lT,_lU){var _lV=B(_9i(_lS)),_lW=new T(function(){return B(_9o(_lV));}),_lX=function(_lY){return new F(function(){return A(_lW,[new T(function(){return B(_lG(_lY));})]);});},_lZ=new T(function(){return B(_lI(_lR,_lS,_lT,new T(function(){return toJSStr(E(_lU));},1)));});return new F(function(){return A(_9m,[_lV,_lZ,_lX]);});},_m0=new T(function(){return B(unCStr("value"));}),_m1=function(_m2,_m3,_m4){var _m5=E(_m4);if(!_m5[0]){return [0];}else{var _m6=_m5[1],_m7=_m5[2];return (!B(A(_m2,[_m6])))?[1,_m6,new T(function(){return B(_m1(_m2,_m3,_m7));})]:[1,new T(function(){return B(A(_m3,[_m6]));}),new T(function(){return B(_m1(_m2,_m3,_m7));})];}},_m8=function(_m9,_ma,_mb,_mc,_){var _md=B(A(_lQ,[_S,_6B,_mb,_m0,_])),_me=_md,_mf=E(_ma),_mg=rMV(_mf),_mh=E(_mg),_mi=new T(function(){return B(_m1(function(_mj){return new F(function(){return _6O(_mj,_mc);});},function(_mk){var _ml=E(_mk);return [0,_ml[1],_ml[2],_me];},_mh[2]));}),_=wMV(_mf,[0,_mh[1],_mi,_mh[3],_mh[4],_mh[5],_mh[6],_mh[7],_mh[8]]);return new F(function(){return A(_m9,[_]);});},_mm=function(_mn,_mo,_mp,_){var _mq=rMV(_mo),_mr=_mq,_ms=E(_mn),_mt=rMV(_ms),_mu=_mt,_mv=B(A(_fn,[_6B,_ja,_])),_mw=E(_mv);if(!_mw[0]){return new F(function(){return die(_j9);});}else{var _mx=E(_mw[1]),_my=E(_N),_mz=_my(_mx);if(!_mz){return new F(function(){return die(_j9);});}else{var _mA=E(_M),_mB=_mA(_mx),_mC=_mB,_mD=B(A(_fn,[_6B,_j6,_])),_mE=function(_,_mF){var _mG=E(_mF);if(!_mG[0]){return new F(function(){return die(_j5);});}else{var _mH=B(A(_iT,[_])),_mI=E(_mH);if(!_mI[0]){return new F(function(){return die(_j2);});}else{var _mJ=B(A(_iR,[_])),_mK=E(_mJ);if(!_mK[0]){return new F(function(){return die(_iZ);});}else{var _mL=E(_mu),_mM=E(_mL[3]),_mN=E(_1)(E(_mK[1]),toJSStr(E(_iP)),toJSStr(_mM)),_mO=B(A(_iO,[_])),_mP=E(_mO);if(!_mP[0]){return new F(function(){return die(_iW);});}else{var _mQ=_mP[1],_mR=function(_){var _mS=function(_mT,_){var _mU=rMV(_ms),_mV=E(_mU),_=wMV(_ms,[0,_mV[1],new T(function(){return B(_ii(_6O,_mT,_mV[2]));}),_mV[3],_mV[4],_mV[5],_mV[6],_mV[7],_mV[8]]);return new F(function(){return _mm(_ms,_mo,_mp,_);});},_mW=function(_){return new F(function(){return _mm(_ms,_mo,_mp,_);});},_mX=B(_cD(function(_mY,_mZ,_){return new F(function(){return _m8(_mW,_ms,_mY,_mZ,_);});},_mS,_mL,E(_mI[1]),_)),_n0=E(_mp),_n1=rMV(_n0),_n2=_n1,_n3=E(_mG[1]),_n4=_n3[1],_n5=E(_hJ),_n6=_n5(_n3[2]),_n7=function(_n8,_){return new F(function(){return _ec(E(_n2),0,0,E(_n8),_);});},_n9=B(A(_gI,[_iJ,_mr,function(_na,_){return new F(function(){return _dU(_iH,_iH,_n7,E(_na),_);});},_n4,_])),_nb=B(A(_jj,[_mL,_n4,_])),_nc=rMV(_n0),_nd=_nc,_ne=_n5(_mx),_nf=B(_dU(_iH,_iH,function(_ng,_){return new F(function(){return _ec(E(_nd),0,0,E(_ng),_);});},_mC,_)),_nh=new T(function(){var _ni=function(_mZ,_){return new F(function(){return _hE(_mr,_mZ,_);});};return B(_hY(_iF,function(_nj,_){return new F(function(){return _e5(_ni,E(_nj),_);});}));}),_nk=B(A(_iq,[_iG,_nh,_mC,_])),_nl=B(_fB(_iE,new T(function(){return B(_ll(_mL));},1),_)),_nm=new T(function(){return fromJSStr(B(_eU([4,E(B(_7C(_6Y,[1,new T(function(){return [4,E(B(_7g(_mr)))];}),[1,new T(function(){return [4,E(B(_7H(_mL)))];}),_3n]])))])));},1);return new F(function(){return _fB(_iD,_nm,_);});};if(!B(_fh(_mL[2],_mM,_mL[8]))){var _nn=E(_9t)(E(_mQ),toJSStr(E(_iL)),toJSStr(E(_iM)));return new F(function(){return _mR(_);});}else{var _no=E(_9t)(E(_mQ),toJSStr(E(_iL)),toJSStr(E(_iK)));return new F(function(){return _mR(_);});}}}}}},_np=E(_mD);if(!_np[0]){return new F(function(){return _mE(_,_6t);});}else{var _nq=E(_np[1]),_nr=_my(_nq);if(!_nr){return new F(function(){return _mE(_,_6t);});}else{var _ns=_mA(_nq);return new F(function(){return _mE(_,[1,[0,_ns,_nq]]);});}}}}},_nt=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:101:3-9"));}),_nu=[0,_6t,_6u,_3n,_nt,_6t,_6t],_nv=new T(function(){return B(_6r(_nu));}),_nw=function(_){return new F(function(){return die(_nv);});},_nx=2,_ny=function(_nz){return E(_nz)[2];},_nA=function(_){return _6t;},_nB=function(_nC,_){return new F(function(){return _nA(_);});},_nD=[0,_ny,_nB],_nE=function(_nF,_nG){while(1){var _nH=E(_nF);if(!_nH[0]){return E(_nG);}else{var _nI=_nH[2],_nJ=E(_nH[1]);if(_nG>_nJ){_nF=_nI;_nG=_nJ;continue;}else{_nF=_nI;continue;}}}},_nK=function(_nL,_nM,_nN){var _nO=E(_nL);if(_nN>_nO){return new F(function(){return _nE(_nM,_nO);});}else{return new F(function(){return _nE(_nM,_nN);});}},_nP=2,_nQ=4,_nR=3,_nS=function(_nT,_nU){var _nV=function(_nW,_nX){while(1){var _nY=B((function(_nZ,_o0){var _o1=E(_nZ);if(!_o1[0]){return [0];}else{var _o2=_o1[2];if(!B(A(_nT,[_o1[1]]))){var _o3=_o0+1|0;_nW=_o2;_nX=_o3;return null;}else{return [1,_o0,new T(function(){return B(_nV(_o2,_o0+1|0));})];}}})(_nW,_nX));if(_nY!=null){return _nY;}}},_o4=B(_nV(_nU,0));return (_o4[0]==0)?[0]:[1,_o4[1]];},_o5=function(_o6){return E(_o6);},_o7=function(_o8,_o9,_oa,_){var _ob=function(_oc,_){var _od=E(_o8),_oe=rMV(_od),_of=E(E(_oe)[2]),_og=new T(function(){var _oh=new T(function(){var _oi=E(E(_oc)[1]);return [0,new T(function(){return B(_o5(_oi[1]));}),new T(function(){return B(_o5(_oi[2]));})];}),_oj=new T(function(){var _ok=E(_oh),_ol=E(_of[1]);return Math.pow(E(_ok[1])-E(_ol[1]),2)+Math.pow(E(_ok[2])-E(_ol[2]),2);}),_om=new T(function(){var _on=E(_oh),_oo=E(_of[2]);return Math.pow(E(_on[1])-E(_oo[1]),2)+Math.pow(E(_on[2])-E(_oo[2]),2);}),_op=[1,new T(function(){var _oq=E(_oh),_or=E(_of[3]);return Math.pow(E(_oq[1])-E(_or[1]),2)+Math.pow(E(_oq[2])-E(_or[2]),2);}),[1,new T(function(){var _os=E(_oh),_ot=E(_of[4]);return Math.pow(E(_os[1])-E(_ot[1]),2)+Math.pow(E(_os[2])-E(_ot[2]),2);}),_3n]],_ou=new T(function(){return B(_nK(_om,_op,E(_oj)));}),_ov=B(_nS(function(_ow){return E(_ou)==E(_ow);},[1,_oj,[1,_om,_op]]));if(!_ov[0]){return 3;}else{switch(E(_ov[1])){case 0:return 0;break;case 1:return 2;break;case 3:return 1;break;default:return 3;}}}),_=wMV(_od,[0,[1,_og],_of]);return new F(function(){return A(_oa,[_]);});},_ox=B(A(_c2,[_6C,_nD,_9g,_o9,_nP,_ob,_])),_oy=B(A(_c2,[_6C,_nD,_9g,_o9,_nR,function(_oz,_){var _oA=E(_o8),_oB=rMV(_oA),_=wMV(_oA,[0,_1Q,E(_oB)[2]]);return new F(function(){return A(_oa,[_]);});},_])),_oC=function(_oD,_){var _oE=E(_o8),_oF=rMV(_oE),_oG=E(_oF),_oH=_oG[2],_oI=E(_oG[1]);if(!_oI[0]){var _oJ=E(_oG);}else{var _oK=new T(function(){var _oL=E(E(_oD)[1]);return [0,new T(function(){return B(_o5(_oL[1]));}),new T(function(){return B(_o5(_oL[2]));})];});switch(E(_oI[1])){case 0:var _oM=E(_oH),_oN=[0,_oI,[0,_oK,_oM[2],_oM[3],_oM[4]]];break;case 1:var _oO=E(_oH),_oN=[0,_oI,[0,_oO[1],_oO[2],_oO[3],_oK]];break;case 2:var _oP=E(_oH),_oN=[0,_oI,[0,_oP[1],_oK,_oP[3],_oP[4]]];break;default:var _oQ=E(_oH),_oN=[0,_oI,[0,_oQ[1],_oQ[2],_oK,_oQ[4]]];}var _oJ=_oN;}var _=wMV(_oE,_oJ);return new F(function(){return A(_oa,[_]);});},_oR=B(A(_c2,[_6C,_nD,_9g,_o9,_nQ,_oC,_]));return _a;},_oS=function(_oT,_oU,_oV,_oW,_oX,_oY,_oZ,_p0,_p1){if(!E(_oU)){return [0,_2W,_oV,_oW,_oX,_oY,_oZ,_p0,_p1];}else{var _p2=E(_oV);if(!_p2[0]){return [0,_2U,_3n,_oW,_oX,_oY,_oZ,_p0,_p1];}else{var _p3=new T(function(){return E(E(_p2[1])[1]);});return [0,_2U,[1,[0,_p3,new T(function(){var _p4=E(_p3),_p5=_p4[1],_p6=E(E(_oT)[1]),_p7=_p6[1],_p8=E(_p6[2]),_p9=E(_p4[2]),_pa=_p8-_p9;if(!_pa){var _pb=E(_p7),_pc=E(_p5),_pd=_pb-_pc;if(!_pd){return [0,_pb,_p9];}else{if(_pd<=0){if(0<= -_pd){return [0,_pb,_p9];}else{return [0,_pc,_p8];}}else{if(0<=_pd){return [0,_pb,_p9];}else{return [0,_pc,_p8];}}}}else{if(_pa<=0){var _pe=E(_p7),_pf=E(_p5),_pg=_pe-_pf;if(!_pg){if( -_pa<=0){return [0,_pe,_p9];}else{return [0,_pf,_p8];}}else{if(_pg<=0){if( -_pa<= -_pg){return [0,_pe,_p9];}else{return [0,_pf,_p8];}}else{if( -_pa<=_pg){return [0,_pe,_p9];}else{return [0,_pf,_p8];}}}}else{var _ph=E(_p7),_pi=E(_p5),_pj=_ph-_pi;if(!_pj){return [0,_pi,_p8];}else{if(_pj<=0){if(_pa<= -_pj){return [0,_ph,_p9];}else{return [0,_pi,_p8];}}else{if(_pa<=_pj){return [0,_ph,_p9];}else{return [0,_pi,_p8];}}}}}}),_3n],_p2[2]],_oW,_oX,_oY,_oZ,_p0,_p1];}}},_pk=function(_pl,_pm,_pn,_){var _po=function(_pp,_){var _pq=E(_pl),_pr=rMV(_pq),_ps=E(_pr),_pt=new T(function(){var _pu=E(E(_pp)[1]);return [0,new T(function(){return B(_o5(_pu[1]));}),new T(function(){return B(_o5(_pu[2]));})];}),_=wMV(_pq,[0,_2U,[1,[0,_pt,_pt,_3n],_ps[2]],_ps[3],_ps[4],_ps[5],_ps[6],_ps[7],_ps[8]]);return new F(function(){return A(_pn,[_]);});},_pv=B(A(_c2,[_6C,_nD,_9g,_pm,_nP,_po,_])),_pw=B(A(_c2,[_6C,_nD,_9g,_pm,_nR,function(_px,_){var _py=E(_pl),_pz=rMV(_py),_pA=E(_pz),_pB=B(_oS(_px,_pA[1],_pA[2],_pA[3],_pA[4],_pA[5],_pA[6],_pA[7],_pA[8])),_=wMV(_py,[0,_2W,_pB[2],_pB[3],_pB[4],_pB[5],_pB[6],_pB[7],_pB[8]]);return new F(function(){return A(_pn,[_]);});},_])),_pC=B(A(_c2,[_6C,_nD,_9g,_pm,_nQ,function(_pD,_){var _pE=E(_pl),_pF=rMV(_pE),_pG=E(_pF),_pH=B(_oS(_pD,_pG[1],_pG[2],_pG[3],_pG[4],_pG[5],_pG[6],_pG[7],_pG[8])),_=wMV(_pE,[0,_pH[1],_pH[2],_pH[3],_pH[4],_pH[5],_pH[6],_pH[7],_pH[8]]);return new F(function(){return A(_pn,[_]);});},_]));return _a;},_pI=new T(function(){return document;}),_pJ=function(_pK,_){var _pL=E(_pK);if(!_pL[0]){return _3n;}else{var _pM=B(_pJ(_pL[2],_));return [1,_pL[1],_pM];}},_pN=function(_pO,_){var _pP=__arr2lst(0,_pO);return new F(function(){return _pJ(_pP,_);});},_pQ=(function(e,q){if(!e || typeof e.querySelectorAll !== 'function') {return [];} else {return e.querySelectorAll(q);}}),_pR=function(_pS,_pT,_pU){var _pV=function(_){var _pW=E(_pQ)(E(_pT),toJSStr(E(_pU)));return new F(function(){return _pN(_pW,_);});};return new F(function(){return A(_2,[_pS,_pV]);});},_pX=(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);}),_pY=(function(x){return document.getElementById(x).value;}),_pZ=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_q0=new T(function(){return B(err(_pZ));}),_q1=function(_q2){var _q3=E(_q2);return (_q3[0]==0)?E(_q0):E(_q3[1]);},_q4=0,_q5=[0,_q4,_q4],_q6=653,_q7=[0,_q6,_q4],_q8=986,_q9=[0,_q6,_q8],_qa=[0,_q4,_q8],_qb=[0,_q5,_qa,_q9,_q7],_qc=[0,_1Q,_qb],_qd=90,_qe=[1,_qd,_3n],_qf=45,_qg=[1,_qf,_qe],_qh=0,_qi=[1,_qh,_qg],_qj=50,_qk=[0,_2W,_3n,_3n,_qh,_qj,_qh,_2M,_qi],_ql=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_qm=new T(function(){return B(err(_ql));}),_qn=new T(function(){return B(unCStr(".json"));}),_qo="saveLink",_qp=new T(function(){return B(unCStr("filePath"));}),_qq=new T(function(){return B(unCStr("input[name=\'mount\']"));}),_qr=new T(function(){return B(unCStr("IndianRoller2.jpg"));}),_qs="loadPath",_qt="filePath",_qu=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_qv=new T(function(){return B(err(_qu));}),_qw=new T(function(){return B(unCStr("Control.Exception.Base"));}),_qx=new T(function(){return B(unCStr("base"));}),_qy=new T(function(){return B(unCStr("PatternMatchFail"));}),_qz=new T(function(){var _qA=hs_wordToWord64(18445595),_qB=hs_wordToWord64(52003073);return [0,_qA,_qB,[0,_qA,_qB,_qx,_qw,_qy],_3n,_3n];}),_qC=function(_qD){return E(_qz);},_qE=function(_qF){var _qG=E(_qF);return new F(function(){return _50(B(_4Y(_qG[1])),_qC,_qG[2]);});},_qH=function(_qI){return E(E(_qI)[1]);},_qJ=function(_qK){return [0,_qL,_qK];},_qM=function(_qN,_qO){return new F(function(){return _16(E(_qN)[1],_qO);});},_qP=function(_qQ,_qR){return new F(function(){return _6b(_qM,_qQ,_qR);});},_qS=function(_qT,_qU,_qV){return new F(function(){return _16(E(_qU)[1],_qV);});},_qW=[0,_qS,_qH,_qP],_qL=new T(function(){return [0,_qC,_qW,_qJ,_qE,_qH];}),_qX=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_qY=function(_qZ){return E(E(_qZ)[3]);},_r0=function(_r1,_r2){return new F(function(){return die(new T(function(){return B(A(_qY,[_r2,_r1]));}));});},_r3=function(_r4,_r5){return new F(function(){return _r0(_r4,_r5);});},_r6=function(_r7,_r8){var _r9=E(_r8);if(!_r9[0]){return [0,_3n,_3n];}else{var _ra=_r9[1];if(!B(A(_r7,[_ra]))){return [0,_3n,_r9];}else{var _rb=new T(function(){var _rc=B(_r6(_r7,_r9[2]));return [0,_rc[1],_rc[2]];});return [0,[1,_ra,new T(function(){return E(E(_rb)[1]);})],new T(function(){return E(E(_rb)[2]);})];}}},_rd=32,_re=new T(function(){return B(unCStr("\n"));}),_rf=function(_rg){return (E(_rg)==124)?false:true;},_rh=function(_ri,_rj){var _rk=B(_r6(_rf,B(unCStr(_ri)))),_rl=_rk[1],_rm=function(_rn,_ro){var _rp=new T(function(){var _rq=new T(function(){return B(_16(_rj,new T(function(){return B(_16(_ro,_re));},1)));});return B(unAppCStr(": ",_rq));},1);return new F(function(){return _16(_rn,_rp);});},_rr=E(_rk[2]);if(!_rr[0]){return new F(function(){return _rm(_rl,_3n);});}else{if(E(_rr[1])==124){return new F(function(){return _rm(_rl,[1,_rd,_rr[2]]);});}else{return new F(function(){return _rm(_rl,_3n);});}}},_rs=function(_rt){return new F(function(){return _r3([0,new T(function(){return B(_rh(_rt,_qX));})],_qL);});},_ru=new T(function(){return B(_rs("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_rv=function(_rw,_rx){while(1){var _ry=B((function(_rz,_rA){var _rB=E(_rz);switch(_rB[0]){case 0:var _rC=E(_rA);if(!_rC[0]){return [0];}else{_rw=B(A(_rB[1],[_rC[1]]));_rx=_rC[2];return null;}break;case 1:var _rD=B(A(_rB[1],[_rA])),_rE=_rA;_rw=_rD;_rx=_rE;return null;case 2:return [0];case 3:return [1,[0,_rB[1],_rA],new T(function(){return B(_rv(_rB[2],_rA));})];default:return E(_rB[1]);}})(_rw,_rx));if(_ry!=null){return _ry;}}},_rF=function(_rG,_rH){var _rI=function(_rJ){var _rK=E(_rH);if(_rK[0]==3){return [3,_rK[1],new T(function(){return B(_rF(_rG,_rK[2]));})];}else{var _rL=E(_rG);if(_rL[0]==2){return E(_rK);}else{var _rM=E(_rK);if(_rM[0]==2){return E(_rL);}else{var _rN=function(_rO){var _rP=E(_rM);if(_rP[0]==4){return [1,function(_rQ){return [4,new T(function(){return B(_16(B(_rv(_rL,_rQ)),_rP[1]));})];}];}else{var _rR=E(_rL);if(_rR[0]==1){var _rS=_rR[1],_rT=E(_rP);if(!_rT[0]){return [1,function(_rU){return new F(function(){return _rF(B(A(_rS,[_rU])),_rT);});}];}else{return [1,function(_rV){return new F(function(){return _rF(B(A(_rS,[_rV])),new T(function(){return B(A(_rT[1],[_rV]));}));});}];}}else{var _rW=E(_rP);if(!_rW[0]){return E(_ru);}else{return [1,function(_rX){return new F(function(){return _rF(_rR,new T(function(){return B(A(_rW[1],[_rX]));}));});}];}}}},_rY=E(_rL);switch(_rY[0]){case 1:var _rZ=E(_rM);if(_rZ[0]==4){return [1,function(_s0){return [4,new T(function(){return B(_16(B(_rv(B(A(_rY[1],[_s0])),_s0)),_rZ[1]));})];}];}else{return new F(function(){return _rN(_);});}break;case 4:var _s1=_rY[1],_s2=E(_rM);switch(_s2[0]){case 0:return [1,function(_s3){return [4,new T(function(){return B(_16(_s1,new T(function(){return B(_rv(_s2,_s3));},1)));})];}];case 1:return [1,function(_s4){return [4,new T(function(){return B(_16(_s1,new T(function(){return B(_rv(B(A(_s2[1],[_s4])),_s4));},1)));})];}];default:return [4,new T(function(){return B(_16(_s1,_s2[1]));})];}break;default:return new F(function(){return _rN(_);});}}}}},_s5=E(_rG);switch(_s5[0]){case 0:var _s6=E(_rH);if(!_s6[0]){return [0,function(_s7){return new F(function(){return _rF(B(A(_s5[1],[_s7])),new T(function(){return B(A(_s6[1],[_s7]));}));});}];}else{return new F(function(){return _rI(_);});}break;case 3:return [3,_s5[1],new T(function(){return B(_rF(_s5[2],_rH));})];default:return new F(function(){return _rI(_);});}},_s8=new T(function(){return B(unCStr("("));}),_s9=new T(function(){return B(unCStr(")"));}),_sa=function(_sb,_sc){while(1){var _sd=E(_sb);if(!_sd[0]){return (E(_sc)[0]==0)?true:false;}else{var _se=E(_sc);if(!_se[0]){return false;}else{if(E(_sd[1])!=E(_se[1])){return false;}else{_sb=_sd[2];_sc=_se[2];continue;}}}}},_sf=function(_sg,_sh){return (!B(_sa(_sg,_sh)))?true:false;},_si=[0,_sa,_sf],_sj=function(_sk,_sl){var _sm=E(_sk);switch(_sm[0]){case 0:return [0,function(_sn){return new F(function(){return _sj(B(A(_sm[1],[_sn])),_sl);});}];case 1:return [1,function(_so){return new F(function(){return _sj(B(A(_sm[1],[_so])),_sl);});}];case 2:return [2];case 3:return new F(function(){return _rF(B(A(_sl,[_sm[1]])),new T(function(){return B(_sj(_sm[2],_sl));}));});break;default:var _sp=function(_sq){var _sr=E(_sq);if(!_sr[0]){return [0];}else{var _ss=E(_sr[1]);return new F(function(){return _16(B(_rv(B(A(_sl,[_ss[1]])),_ss[2])),new T(function(){return B(_sp(_sr[2]));},1));});}},_st=B(_sp(_sm[1]));return (_st[0]==0)?[2]:[4,_st];}},_su=[2],_sv=function(_sw){return [3,_sw,_su];},_sx=function(_sy,_sz){var _sA=E(_sy);if(!_sA){return new F(function(){return A(_sz,[_a]);});}else{var _sB=new T(function(){return B(_sx(_sA-1|0,_sz));});return [0,function(_sC){return E(_sB);}];}},_sD=function(_sE,_sF,_sG){var _sH=new T(function(){return B(A(_sE,[_sv]));}),_sI=function(_sJ,_sK,_sL,_sM){while(1){var _sN=B((function(_sO,_sP,_sQ,_sR){var _sS=E(_sO);switch(_sS[0]){case 0:var _sT=E(_sP);if(!_sT[0]){return new F(function(){return A(_sF,[_sR]);});}else{var _sU=_sQ+1|0,_sV=_sR;_sJ=B(A(_sS[1],[_sT[1]]));_sK=_sT[2];_sL=_sU;_sM=_sV;return null;}break;case 1:var _sW=B(A(_sS[1],[_sP])),_sX=_sP,_sU=_sQ,_sV=_sR;_sJ=_sW;_sK=_sX;_sL=_sU;_sM=_sV;return null;case 2:return new F(function(){return A(_sF,[_sR]);});break;case 3:var _sY=new T(function(){return B(_sj(_sS,_sR));});return new F(function(){return _sx(_sQ,function(_sZ){return E(_sY);});});break;default:return new F(function(){return _sj(_sS,_sR);});}})(_sJ,_sK,_sL,_sM));if(_sN!=null){return _sN;}}};return function(_t0){return new F(function(){return _sI(_sH,_t0,0,_sG);});};},_t1=function(_t2){return new F(function(){return A(_t2,[_3n]);});},_t3=function(_t4,_t5){var _t6=function(_t7){var _t8=E(_t7);if(!_t8[0]){return E(_t1);}else{var _t9=_t8[1];if(!B(A(_t4,[_t9]))){return E(_t1);}else{var _ta=new T(function(){return B(_t6(_t8[2]));}),_tb=function(_tc){var _td=new T(function(){return B(A(_ta,[function(_te){return new F(function(){return A(_tc,[[1,_t9,_te]]);});}]));});return [0,function(_tf){return E(_td);}];};return E(_tb);}}};return function(_tg){return new F(function(){return A(_t6,[_tg,_t5]);});};},_th=[6],_ti=new T(function(){return B(unCStr("valDig: Bad base"));}),_tj=new T(function(){return B(err(_ti));}),_tk=function(_tl,_tm){var _tn=function(_to,_tp){var _tq=E(_to);if(!_tq[0]){var _tr=new T(function(){return B(A(_tp,[_3n]));});return function(_ts){return new F(function(){return A(_ts,[_tr]);});};}else{var _tt=E(_tq[1]),_tu=function(_tv){var _tw=new T(function(){return B(_tn(_tq[2],function(_tx){return new F(function(){return A(_tp,[[1,_tv,_tx]]);});}));}),_ty=function(_tz){var _tA=new T(function(){return B(A(_tw,[_tz]));});return [0,function(_tB){return E(_tA);}];};return E(_ty);};switch(E(_tl)){case 8:if(48>_tt){var _tC=new T(function(){return B(A(_tp,[_3n]));});return function(_tD){return new F(function(){return A(_tD,[_tC]);});};}else{if(_tt>55){var _tE=new T(function(){return B(A(_tp,[_3n]));});return function(_tF){return new F(function(){return A(_tF,[_tE]);});};}else{return new F(function(){return _tu(_tt-48|0);});}}break;case 10:if(48>_tt){var _tG=new T(function(){return B(A(_tp,[_3n]));});return function(_tH){return new F(function(){return A(_tH,[_tG]);});};}else{if(_tt>57){var _tI=new T(function(){return B(A(_tp,[_3n]));});return function(_tJ){return new F(function(){return A(_tJ,[_tI]);});};}else{return new F(function(){return _tu(_tt-48|0);});}}break;case 16:if(48>_tt){if(97>_tt){if(65>_tt){var _tK=new T(function(){return B(A(_tp,[_3n]));});return function(_tL){return new F(function(){return A(_tL,[_tK]);});};}else{if(_tt>70){var _tM=new T(function(){return B(A(_tp,[_3n]));});return function(_tN){return new F(function(){return A(_tN,[_tM]);});};}else{return new F(function(){return _tu((_tt-65|0)+10|0);});}}}else{if(_tt>102){if(65>_tt){var _tO=new T(function(){return B(A(_tp,[_3n]));});return function(_tP){return new F(function(){return A(_tP,[_tO]);});};}else{if(_tt>70){var _tQ=new T(function(){return B(A(_tp,[_3n]));});return function(_tR){return new F(function(){return A(_tR,[_tQ]);});};}else{return new F(function(){return _tu((_tt-65|0)+10|0);});}}}else{return new F(function(){return _tu((_tt-97|0)+10|0);});}}}else{if(_tt>57){if(97>_tt){if(65>_tt){var _tS=new T(function(){return B(A(_tp,[_3n]));});return function(_tT){return new F(function(){return A(_tT,[_tS]);});};}else{if(_tt>70){var _tU=new T(function(){return B(A(_tp,[_3n]));});return function(_tV){return new F(function(){return A(_tV,[_tU]);});};}else{return new F(function(){return _tu((_tt-65|0)+10|0);});}}}else{if(_tt>102){if(65>_tt){var _tW=new T(function(){return B(A(_tp,[_3n]));});return function(_tX){return new F(function(){return A(_tX,[_tW]);});};}else{if(_tt>70){var _tY=new T(function(){return B(A(_tp,[_3n]));});return function(_tZ){return new F(function(){return A(_tZ,[_tY]);});};}else{return new F(function(){return _tu((_tt-65|0)+10|0);});}}}else{return new F(function(){return _tu((_tt-97|0)+10|0);});}}}else{return new F(function(){return _tu(_tt-48|0);});}}break;default:return E(_tj);}}},_u0=function(_u1){var _u2=E(_u1);if(!_u2[0]){return [2];}else{return new F(function(){return A(_tm,[_u2]);});}};return function(_u3){return new F(function(){return A(_tn,[_u3,_Q,_u0]);});};},_u4=16,_u5=8,_u6=function(_u7){var _u8=function(_u9){return new F(function(){return A(_u7,[[5,[0,_u5,_u9]]]);});},_ua=function(_ub){return new F(function(){return A(_u7,[[5,[0,_u4,_ub]]]);});},_uc=function(_ud){switch(E(_ud)){case 79:return [1,B(_tk(_u5,_u8))];case 88:return [1,B(_tk(_u4,_ua))];case 111:return [1,B(_tk(_u5,_u8))];case 120:return [1,B(_tk(_u4,_ua))];default:return [2];}};return function(_ue){return (E(_ue)==48)?[0,_uc]:[2];};},_uf=function(_ug){return [0,B(_u6(_ug))];},_uh=function(_ui){return new F(function(){return A(_ui,[_6t]);});},_uj=function(_uk){return new F(function(){return A(_uk,[_6t]);});},_ul=10,_um=[0,1],_un=[0,2147483647],_uo=function(_up,_uq){while(1){var _ur=E(_up);if(!_ur[0]){var _us=_ur[1],_ut=E(_uq);if(!_ut[0]){var _uu=_ut[1],_uv=addC(_us,_uu);if(!E(_uv[2])){return [0,_uv[1]];}else{_up=[1,I_fromInt(_us)];_uq=[1,I_fromInt(_uu)];continue;}}else{_up=[1,I_fromInt(_us)];_uq=_ut;continue;}}else{var _uw=E(_uq);if(!_uw[0]){_up=_ur;_uq=[1,I_fromInt(_uw[1])];continue;}else{return [1,I_add(_ur[1],_uw[1])];}}}},_ux=new T(function(){return B(_uo(_un,_um));}),_uy=function(_uz){var _uA=E(_uz);if(!_uA[0]){var _uB=E(_uA[1]);return (_uB==(-2147483648))?E(_ux):[0, -_uB];}else{return [1,I_negate(_uA[1])];}},_uC=[0,10],_uD=function(_uE,_uF){while(1){var _uG=E(_uE);if(!_uG[0]){return E(_uF);}else{var _uH=_uF+1|0;_uE=_uG[2];_uF=_uH;continue;}}},_uI=function(_uJ){return new F(function(){return _bz(E(_uJ));});},_uK=new T(function(){return B(unCStr("this should not happen"));}),_uL=new T(function(){return B(err(_uK));}),_uM=function(_uN,_uO){while(1){var _uP=E(_uN);if(!_uP[0]){var _uQ=_uP[1],_uR=E(_uO);if(!_uR[0]){var _uS=_uR[1];if(!(imul(_uQ,_uS)|0)){return [0,imul(_uQ,_uS)|0];}else{_uN=[1,I_fromInt(_uQ)];_uO=[1,I_fromInt(_uS)];continue;}}else{_uN=[1,I_fromInt(_uQ)];_uO=_uR;continue;}}else{var _uT=E(_uO);if(!_uT[0]){_uN=_uP;_uO=[1,I_fromInt(_uT[1])];continue;}else{return [1,I_mul(_uP[1],_uT[1])];}}}},_uU=function(_uV,_uW){var _uX=E(_uW);if(!_uX[0]){return [0];}else{var _uY=E(_uX[2]);return (_uY[0]==0)?E(_uL):[1,B(_uo(B(_uM(_uX[1],_uV)),_uY[1])),new T(function(){return B(_uU(_uV,_uY[2]));})];}},_uZ=[0,0],_v0=function(_v1,_v2,_v3){while(1){var _v4=B((function(_v5,_v6,_v7){var _v8=E(_v7);if(!_v8[0]){return E(_uZ);}else{if(!E(_v8[2])[0]){return E(_v8[1]);}else{var _v9=E(_v6);if(_v9<=40){var _va=_uZ,_vb=_v8;while(1){var _vc=E(_vb);if(!_vc[0]){return E(_va);}else{var _vd=B(_uo(B(_uM(_va,_v5)),_vc[1]));_va=_vd;_vb=_vc[2];continue;}}}else{var _ve=B(_uM(_v5,_v5));if(!(_v9%2)){var _vf=B(_uU(_v5,_v8));_v1=_ve;_v2=quot(_v9+1|0,2);_v3=_vf;return null;}else{var _vf=B(_uU(_v5,[1,_uZ,_v8]));_v1=_ve;_v2=quot(_v9+1|0,2);_v3=_vf;return null;}}}}})(_v1,_v2,_v3));if(_v4!=null){return _v4;}}},_vg=function(_vh,_vi){return new F(function(){return _v0(_vh,new T(function(){return B(_uD(_vi,0));},1),B(_1A(_uI,_vi)));});},_vj=function(_vk){var _vl=new T(function(){var _vm=new T(function(){var _vn=function(_vo){return new F(function(){return A(_vk,[[1,new T(function(){return B(_vg(_uC,_vo));})]]);});};return [1,B(_tk(_ul,_vn))];}),_vp=function(_vq){if(E(_vq)==43){var _vr=function(_vs){return new F(function(){return A(_vk,[[1,new T(function(){return B(_vg(_uC,_vs));})]]);});};return [1,B(_tk(_ul,_vr))];}else{return [2];}},_vt=function(_vu){if(E(_vu)==45){var _vv=function(_vw){return new F(function(){return A(_vk,[[1,new T(function(){return B(_uy(B(_vg(_uC,_vw))));})]]);});};return [1,B(_tk(_ul,_vv))];}else{return [2];}};return B(_rF(B(_rF([0,_vt],[0,_vp])),_vm));});return new F(function(){return _rF([0,function(_vx){return (E(_vx)==101)?E(_vl):[2];}],[0,function(_vy){return (E(_vy)==69)?E(_vl):[2];}]);});},_vz=function(_vA){var _vB=function(_vC){return new F(function(){return A(_vA,[[1,_vC]]);});};return function(_vD){return (E(_vD)==46)?[1,B(_tk(_ul,_vB))]:[2];};},_vE=function(_vF){return [0,B(_vz(_vF))];},_vG=function(_vH){var _vI=function(_vJ){var _vK=function(_vL){return [1,B(_sD(_vj,_uh,function(_vM){return new F(function(){return A(_vH,[[5,[1,_vJ,_vL,_vM]]]);});}))];};return [1,B(_sD(_vE,_uj,_vK))];};return new F(function(){return _tk(_ul,_vI);});},_vN=function(_vO){return [1,B(_vG(_vO))];},_vP=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_vQ=function(_vR){return new F(function(){return _f5(_f4,_vR,_vP);});},_vS=false,_vT=true,_vU=function(_vV){var _vW=new T(function(){return B(A(_vV,[_u5]));}),_vX=new T(function(){return B(A(_vV,[_u4]));});return function(_vY){switch(E(_vY)){case 79:return E(_vW);case 88:return E(_vX);case 111:return E(_vW);case 120:return E(_vX);default:return [2];}};},_vZ=function(_w0){return [0,B(_vU(_w0))];},_w1=function(_w2){return new F(function(){return A(_w2,[_ul]);});},_w3=function(_w4){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_7U(9,_w4,_3n));}))));});},_w5=function(_w6){var _w7=E(_w6);if(!_w7[0]){return E(_w7[1]);}else{return new F(function(){return I_toInt(_w7[1]);});}},_w8=function(_w9,_wa){var _wb=E(_w9);if(!_wb[0]){var _wc=_wb[1],_wd=E(_wa);return (_wd[0]==0)?_wc<=_wd[1]:I_compareInt(_wd[1],_wc)>=0;}else{var _we=_wb[1],_wf=E(_wa);return (_wf[0]==0)?I_compareInt(_we,_wf[1])<=0:I_compare(_we,_wf[1])<=0;}},_wg=function(_wh){return [2];},_wi=function(_wj){var _wk=E(_wj);if(!_wk[0]){return E(_wg);}else{var _wl=_wk[1],_wm=E(_wk[2]);if(!_wm[0]){return E(_wl);}else{var _wn=new T(function(){return B(_wi(_wm));}),_wo=function(_wp){return new F(function(){return _rF(B(A(_wl,[_wp])),new T(function(){return B(A(_wn,[_wp]));}));});};return E(_wo);}}},_wq=function(_wr,_ws){var _wt=function(_wu,_wv,_ww){var _wx=E(_wu);if(!_wx[0]){return new F(function(){return A(_ww,[_wr]);});}else{var _wy=E(_wv);if(!_wy[0]){return [2];}else{if(E(_wx[1])!=E(_wy[1])){return [2];}else{var _wz=new T(function(){return B(_wt(_wx[2],_wy[2],_ww));});return [0,function(_wA){return E(_wz);}];}}}};return function(_wB){return new F(function(){return _wt(_wr,_wB,_ws);});};},_wC=new T(function(){return B(unCStr("SO"));}),_wD=14,_wE=function(_wF){var _wG=new T(function(){return B(A(_wF,[_wD]));});return [1,B(_wq(_wC,function(_wH){return E(_wG);}))];},_wI=new T(function(){return B(unCStr("SOH"));}),_wJ=1,_wK=function(_wL){var _wM=new T(function(){return B(A(_wL,[_wJ]));});return [1,B(_wq(_wI,function(_wN){return E(_wM);}))];},_wO=function(_wP){return [1,B(_sD(_wK,_wE,_wP))];},_wQ=new T(function(){return B(unCStr("NUL"));}),_wR=0,_wS=function(_wT){var _wU=new T(function(){return B(A(_wT,[_wR]));});return [1,B(_wq(_wQ,function(_wV){return E(_wU);}))];},_wW=new T(function(){return B(unCStr("STX"));}),_wX=2,_wY=function(_wZ){var _x0=new T(function(){return B(A(_wZ,[_wX]));});return [1,B(_wq(_wW,function(_x1){return E(_x0);}))];},_x2=new T(function(){return B(unCStr("ETX"));}),_x3=3,_x4=function(_x5){var _x6=new T(function(){return B(A(_x5,[_x3]));});return [1,B(_wq(_x2,function(_x7){return E(_x6);}))];},_x8=new T(function(){return B(unCStr("EOT"));}),_x9=4,_xa=function(_xb){var _xc=new T(function(){return B(A(_xb,[_x9]));});return [1,B(_wq(_x8,function(_xd){return E(_xc);}))];},_xe=new T(function(){return B(unCStr("ENQ"));}),_xf=5,_xg=function(_xh){var _xi=new T(function(){return B(A(_xh,[_xf]));});return [1,B(_wq(_xe,function(_xj){return E(_xi);}))];},_xk=new T(function(){return B(unCStr("ACK"));}),_xl=6,_xm=function(_xn){var _xo=new T(function(){return B(A(_xn,[_xl]));});return [1,B(_wq(_xk,function(_xp){return E(_xo);}))];},_xq=new T(function(){return B(unCStr("BEL"));}),_xr=7,_xs=function(_xt){var _xu=new T(function(){return B(A(_xt,[_xr]));});return [1,B(_wq(_xq,function(_xv){return E(_xu);}))];},_xw=new T(function(){return B(unCStr("BS"));}),_xx=8,_xy=function(_xz){var _xA=new T(function(){return B(A(_xz,[_xx]));});return [1,B(_wq(_xw,function(_xB){return E(_xA);}))];},_xC=new T(function(){return B(unCStr("HT"));}),_xD=9,_xE=function(_xF){var _xG=new T(function(){return B(A(_xF,[_xD]));});return [1,B(_wq(_xC,function(_xH){return E(_xG);}))];},_xI=new T(function(){return B(unCStr("LF"));}),_xJ=10,_xK=function(_xL){var _xM=new T(function(){return B(A(_xL,[_xJ]));});return [1,B(_wq(_xI,function(_xN){return E(_xM);}))];},_xO=new T(function(){return B(unCStr("VT"));}),_xP=11,_xQ=function(_xR){var _xS=new T(function(){return B(A(_xR,[_xP]));});return [1,B(_wq(_xO,function(_xT){return E(_xS);}))];},_xU=new T(function(){return B(unCStr("FF"));}),_xV=12,_xW=function(_xX){var _xY=new T(function(){return B(A(_xX,[_xV]));});return [1,B(_wq(_xU,function(_xZ){return E(_xY);}))];},_y0=new T(function(){return B(unCStr("CR"));}),_y1=13,_y2=function(_y3){var _y4=new T(function(){return B(A(_y3,[_y1]));});return [1,B(_wq(_y0,function(_y5){return E(_y4);}))];},_y6=new T(function(){return B(unCStr("SI"));}),_y7=15,_y8=function(_y9){var _ya=new T(function(){return B(A(_y9,[_y7]));});return [1,B(_wq(_y6,function(_yb){return E(_ya);}))];},_yc=new T(function(){return B(unCStr("DLE"));}),_yd=16,_ye=function(_yf){var _yg=new T(function(){return B(A(_yf,[_yd]));});return [1,B(_wq(_yc,function(_yh){return E(_yg);}))];},_yi=new T(function(){return B(unCStr("DC1"));}),_yj=17,_yk=function(_yl){var _ym=new T(function(){return B(A(_yl,[_yj]));});return [1,B(_wq(_yi,function(_yn){return E(_ym);}))];},_yo=new T(function(){return B(unCStr("DC2"));}),_yp=18,_yq=function(_yr){var _ys=new T(function(){return B(A(_yr,[_yp]));});return [1,B(_wq(_yo,function(_yt){return E(_ys);}))];},_yu=new T(function(){return B(unCStr("DC3"));}),_yv=19,_yw=function(_yx){var _yy=new T(function(){return B(A(_yx,[_yv]));});return [1,B(_wq(_yu,function(_yz){return E(_yy);}))];},_yA=new T(function(){return B(unCStr("DC4"));}),_yB=20,_yC=function(_yD){var _yE=new T(function(){return B(A(_yD,[_yB]));});return [1,B(_wq(_yA,function(_yF){return E(_yE);}))];},_yG=new T(function(){return B(unCStr("NAK"));}),_yH=21,_yI=function(_yJ){var _yK=new T(function(){return B(A(_yJ,[_yH]));});return [1,B(_wq(_yG,function(_yL){return E(_yK);}))];},_yM=new T(function(){return B(unCStr("SYN"));}),_yN=22,_yO=function(_yP){var _yQ=new T(function(){return B(A(_yP,[_yN]));});return [1,B(_wq(_yM,function(_yR){return E(_yQ);}))];},_yS=new T(function(){return B(unCStr("ETB"));}),_yT=23,_yU=function(_yV){var _yW=new T(function(){return B(A(_yV,[_yT]));});return [1,B(_wq(_yS,function(_yX){return E(_yW);}))];},_yY=new T(function(){return B(unCStr("CAN"));}),_yZ=24,_z0=function(_z1){var _z2=new T(function(){return B(A(_z1,[_yZ]));});return [1,B(_wq(_yY,function(_z3){return E(_z2);}))];},_z4=new T(function(){return B(unCStr("EM"));}),_z5=25,_z6=function(_z7){var _z8=new T(function(){return B(A(_z7,[_z5]));});return [1,B(_wq(_z4,function(_z9){return E(_z8);}))];},_za=new T(function(){return B(unCStr("SUB"));}),_zb=26,_zc=function(_zd){var _ze=new T(function(){return B(A(_zd,[_zb]));});return [1,B(_wq(_za,function(_zf){return E(_ze);}))];},_zg=new T(function(){return B(unCStr("ESC"));}),_zh=27,_zi=function(_zj){var _zk=new T(function(){return B(A(_zj,[_zh]));});return [1,B(_wq(_zg,function(_zl){return E(_zk);}))];},_zm=new T(function(){return B(unCStr("FS"));}),_zn=28,_zo=function(_zp){var _zq=new T(function(){return B(A(_zp,[_zn]));});return [1,B(_wq(_zm,function(_zr){return E(_zq);}))];},_zs=new T(function(){return B(unCStr("GS"));}),_zt=29,_zu=function(_zv){var _zw=new T(function(){return B(A(_zv,[_zt]));});return [1,B(_wq(_zs,function(_zx){return E(_zw);}))];},_zy=new T(function(){return B(unCStr("RS"));}),_zz=30,_zA=function(_zB){var _zC=new T(function(){return B(A(_zB,[_zz]));});return [1,B(_wq(_zy,function(_zD){return E(_zC);}))];},_zE=new T(function(){return B(unCStr("US"));}),_zF=31,_zG=function(_zH){var _zI=new T(function(){return B(A(_zH,[_zF]));});return [1,B(_wq(_zE,function(_zJ){return E(_zI);}))];},_zK=new T(function(){return B(unCStr("SP"));}),_zL=32,_zM=function(_zN){var _zO=new T(function(){return B(A(_zN,[_zL]));});return [1,B(_wq(_zK,function(_zP){return E(_zO);}))];},_zQ=new T(function(){return B(unCStr("DEL"));}),_zR=127,_zS=function(_zT){var _zU=new T(function(){return B(A(_zT,[_zR]));});return [1,B(_wq(_zQ,function(_zV){return E(_zU);}))];},_zW=[1,_zS,_3n],_zX=[1,_zM,_zW],_zY=[1,_zG,_zX],_zZ=[1,_zA,_zY],_A0=[1,_zu,_zZ],_A1=[1,_zo,_A0],_A2=[1,_zi,_A1],_A3=[1,_zc,_A2],_A4=[1,_z6,_A3],_A5=[1,_z0,_A4],_A6=[1,_yU,_A5],_A7=[1,_yO,_A6],_A8=[1,_yI,_A7],_A9=[1,_yC,_A8],_Aa=[1,_yw,_A9],_Ab=[1,_yq,_Aa],_Ac=[1,_yk,_Ab],_Ad=[1,_ye,_Ac],_Ae=[1,_y8,_Ad],_Af=[1,_y2,_Ae],_Ag=[1,_xW,_Af],_Ah=[1,_xQ,_Ag],_Ai=[1,_xK,_Ah],_Aj=[1,_xE,_Ai],_Ak=[1,_xy,_Aj],_Al=[1,_xs,_Ak],_Am=[1,_xm,_Al],_An=[1,_xg,_Am],_Ao=[1,_xa,_An],_Ap=[1,_x4,_Ao],_Aq=[1,_wY,_Ap],_Ar=[1,_wS,_Aq],_As=[1,_wO,_Ar],_At=new T(function(){return B(_wi(_As));}),_Au=34,_Av=[0,1114111],_Aw=92,_Ax=39,_Ay=function(_Az){var _AA=new T(function(){return B(A(_Az,[_xr]));}),_AB=new T(function(){return B(A(_Az,[_xx]));}),_AC=new T(function(){return B(A(_Az,[_xD]));}),_AD=new T(function(){return B(A(_Az,[_xJ]));}),_AE=new T(function(){return B(A(_Az,[_xP]));}),_AF=new T(function(){return B(A(_Az,[_xV]));}),_AG=new T(function(){return B(A(_Az,[_y1]));}),_AH=new T(function(){return B(A(_Az,[_Aw]));}),_AI=new T(function(){return B(A(_Az,[_Ax]));}),_AJ=new T(function(){return B(A(_Az,[_Au]));}),_AK=new T(function(){var _AL=function(_AM){var _AN=new T(function(){return B(_bz(E(_AM)));}),_AO=function(_AP){var _AQ=B(_vg(_AN,_AP));if(!B(_w8(_AQ,_Av))){return [2];}else{return new F(function(){return A(_Az,[new T(function(){var _AR=B(_w5(_AQ));if(_AR>>>0>1114111){return B(_w3(_AR));}else{return _AR;}})]);});}};return [1,B(_tk(_AM,_AO))];},_AS=new T(function(){var _AT=new T(function(){return B(A(_Az,[_zF]));}),_AU=new T(function(){return B(A(_Az,[_zz]));}),_AV=new T(function(){return B(A(_Az,[_zt]));}),_AW=new T(function(){return B(A(_Az,[_zn]));}),_AX=new T(function(){return B(A(_Az,[_zh]));}),_AY=new T(function(){return B(A(_Az,[_zb]));}),_AZ=new T(function(){return B(A(_Az,[_z5]));}),_B0=new T(function(){return B(A(_Az,[_yZ]));}),_B1=new T(function(){return B(A(_Az,[_yT]));}),_B2=new T(function(){return B(A(_Az,[_yN]));}),_B3=new T(function(){return B(A(_Az,[_yH]));}),_B4=new T(function(){return B(A(_Az,[_yB]));}),_B5=new T(function(){return B(A(_Az,[_yv]));}),_B6=new T(function(){return B(A(_Az,[_yp]));}),_B7=new T(function(){return B(A(_Az,[_yj]));}),_B8=new T(function(){return B(A(_Az,[_yd]));}),_B9=new T(function(){return B(A(_Az,[_y7]));}),_Ba=new T(function(){return B(A(_Az,[_wD]));}),_Bb=new T(function(){return B(A(_Az,[_xl]));}),_Bc=new T(function(){return B(A(_Az,[_xf]));}),_Bd=new T(function(){return B(A(_Az,[_x9]));}),_Be=new T(function(){return B(A(_Az,[_x3]));}),_Bf=new T(function(){return B(A(_Az,[_wX]));}),_Bg=new T(function(){return B(A(_Az,[_wJ]));}),_Bh=new T(function(){return B(A(_Az,[_wR]));}),_Bi=function(_Bj){switch(E(_Bj)){case 64:return E(_Bh);case 65:return E(_Bg);case 66:return E(_Bf);case 67:return E(_Be);case 68:return E(_Bd);case 69:return E(_Bc);case 70:return E(_Bb);case 71:return E(_AA);case 72:return E(_AB);case 73:return E(_AC);case 74:return E(_AD);case 75:return E(_AE);case 76:return E(_AF);case 77:return E(_AG);case 78:return E(_Ba);case 79:return E(_B9);case 80:return E(_B8);case 81:return E(_B7);case 82:return E(_B6);case 83:return E(_B5);case 84:return E(_B4);case 85:return E(_B3);case 86:return E(_B2);case 87:return E(_B1);case 88:return E(_B0);case 89:return E(_AZ);case 90:return E(_AY);case 91:return E(_AX);case 92:return E(_AW);case 93:return E(_AV);case 94:return E(_AU);case 95:return E(_AT);default:return [2];}};return B(_rF([0,function(_Bk){return (E(_Bk)==94)?[0,_Bi]:[2];}],new T(function(){return B(A(_At,[_Az]));})));});return B(_rF([1,B(_sD(_vZ,_w1,_AL))],_AS));});return new F(function(){return _rF([0,function(_Bl){switch(E(_Bl)){case 34:return E(_AJ);case 39:return E(_AI);case 92:return E(_AH);case 97:return E(_AA);case 98:return E(_AB);case 102:return E(_AF);case 110:return E(_AD);case 114:return E(_AG);case 116:return E(_AC);case 118:return E(_AE);default:return [2];}}],_AK);});},_Bm=function(_Bn){return new F(function(){return A(_Bn,[_a]);});},_Bo=function(_Bp){var _Bq=E(_Bp);if(!_Bq[0]){return E(_Bm);}else{var _Br=E(_Bq[1]),_Bs=_Br>>>0,_Bt=new T(function(){return B(_Bo(_Bq[2]));});if(_Bs>887){var _Bu=u_iswspace(_Br);if(!E(_Bu)){return E(_Bm);}else{var _Bv=function(_Bw){var _Bx=new T(function(){return B(A(_Bt,[_Bw]));});return [0,function(_By){return E(_Bx);}];};return E(_Bv);}}else{var _Bz=E(_Bs);if(_Bz==32){var _BA=function(_BB){var _BC=new T(function(){return B(A(_Bt,[_BB]));});return [0,function(_BD){return E(_BC);}];};return E(_BA);}else{if(_Bz-9>>>0>4){if(E(_Bz)==160){var _BE=function(_BF){var _BG=new T(function(){return B(A(_Bt,[_BF]));});return [0,function(_BH){return E(_BG);}];};return E(_BE);}else{return E(_Bm);}}else{var _BI=function(_BJ){var _BK=new T(function(){return B(A(_Bt,[_BJ]));});return [0,function(_BL){return E(_BK);}];};return E(_BI);}}}}},_BM=function(_BN){var _BO=new T(function(){return B(_BM(_BN));}),_BP=function(_BQ){return (E(_BQ)==92)?E(_BO):[2];},_BR=function(_BS){return [0,_BP];},_BT=[1,function(_BU){return new F(function(){return A(_Bo,[_BU,_BR]);});}],_BV=new T(function(){return B(_Ay(function(_BW){return new F(function(){return A(_BN,[[0,_BW,_vT]]);});}));}),_BX=function(_BY){var _BZ=E(_BY);if(_BZ==38){return E(_BO);}else{var _C0=_BZ>>>0;if(_C0>887){var _C1=u_iswspace(_BZ);return (E(_C1)==0)?[2]:E(_BT);}else{var _C2=E(_C0);return (_C2==32)?E(_BT):(_C2-9>>>0>4)?(E(_C2)==160)?E(_BT):[2]:E(_BT);}}};return new F(function(){return _rF([0,function(_C3){return (E(_C3)==92)?[0,_BX]:[2];}],[0,function(_C4){var _C5=E(_C4);if(E(_C5)==92){return E(_BV);}else{return new F(function(){return A(_BN,[[0,_C5,_vS]]);});}}]);});},_C6=function(_C7,_C8){var _C9=new T(function(){return B(A(_C8,[[1,new T(function(){return B(A(_C7,[_3n]));})]]));}),_Ca=function(_Cb){var _Cc=E(_Cb),_Cd=E(_Cc[1]);if(E(_Cd)==34){if(!E(_Cc[2])){return E(_C9);}else{return new F(function(){return _C6(function(_Ce){return new F(function(){return A(_C7,[[1,_Cd,_Ce]]);});},_C8);});}}else{return new F(function(){return _C6(function(_Cf){return new F(function(){return A(_C7,[[1,_Cd,_Cf]]);});},_C8);});}};return new F(function(){return _BM(_Ca);});},_Cg=new T(function(){return B(unCStr("_\'"));}),_Ch=function(_Ci){var _Cj=u_iswalnum(_Ci);if(!E(_Cj)){return new F(function(){return _f5(_f4,_Ci,_Cg);});}else{return true;}},_Ck=function(_Cl){return new F(function(){return _Ch(E(_Cl));});},_Cm=new T(function(){return B(unCStr(",;()[]{}`"));}),_Cn=new T(function(){return B(unCStr("=>"));}),_Co=[1,_Cn,_3n],_Cp=new T(function(){return B(unCStr("~"));}),_Cq=[1,_Cp,_Co],_Cr=new T(function(){return B(unCStr("@"));}),_Cs=[1,_Cr,_Cq],_Ct=new T(function(){return B(unCStr("->"));}),_Cu=[1,_Ct,_Cs],_Cv=new T(function(){return B(unCStr("<-"));}),_Cw=[1,_Cv,_Cu],_Cx=new T(function(){return B(unCStr("|"));}),_Cy=[1,_Cx,_Cw],_Cz=new T(function(){return B(unCStr("\\"));}),_CA=[1,_Cz,_Cy],_CB=new T(function(){return B(unCStr("="));}),_CC=[1,_CB,_CA],_CD=new T(function(){return B(unCStr("::"));}),_CE=[1,_CD,_CC],_CF=new T(function(){return B(unCStr(".."));}),_CG=[1,_CF,_CE],_CH=function(_CI){var _CJ=new T(function(){return B(A(_CI,[_th]));}),_CK=new T(function(){var _CL=new T(function(){var _CM=function(_CN){var _CO=new T(function(){return B(A(_CI,[[0,_CN]]));});return [0,function(_CP){return (E(_CP)==39)?E(_CO):[2];}];};return B(_Ay(_CM));}),_CQ=function(_CR){var _CS=E(_CR);switch(E(_CS)){case 39:return [2];case 92:return E(_CL);default:var _CT=new T(function(){return B(A(_CI,[[0,_CS]]));});return [0,function(_CU){return (E(_CU)==39)?E(_CT):[2];}];}},_CV=new T(function(){var _CW=new T(function(){return B(_C6(_Q,_CI));}),_CX=new T(function(){var _CY=new T(function(){var _CZ=new T(function(){var _D0=function(_D1){var _D2=E(_D1),_D3=u_iswalpha(_D2);return (E(_D3)==0)?(E(_D2)==95)?[1,B(_t3(_Ck,function(_D4){return new F(function(){return A(_CI,[[3,[1,_D2,_D4]]]);});}))]:[2]:[1,B(_t3(_Ck,function(_D5){return new F(function(){return A(_CI,[[3,[1,_D2,_D5]]]);});}))];};return B(_rF([0,_D0],new T(function(){return [1,B(_sD(_uf,_vN,_CI))];})));}),_D6=function(_D7){return (!B(_f5(_f4,_D7,_vP)))?[2]:[1,B(_t3(_vQ,function(_D8){var _D9=[1,_D7,_D8];if(!B(_f5(_si,_D9,_CG))){return new F(function(){return A(_CI,[[4,_D9]]);});}else{return new F(function(){return A(_CI,[[2,_D9]]);});}}))];};return B(_rF([0,_D6],_CZ));});return B(_rF([0,function(_Da){if(!B(_f5(_f4,_Da,_Cm))){return [2];}else{return new F(function(){return A(_CI,[[2,[1,_Da,_3n]]]);});}}],_CY));});return B(_rF([0,function(_Db){return (E(_Db)==34)?E(_CW):[2];}],_CX));});return B(_rF([0,function(_Dc){return (E(_Dc)==39)?[0,_CQ]:[2];}],_CV));});return new F(function(){return _rF([1,function(_Dd){return (E(_Dd)[0]==0)?E(_CJ):[2];}],_CK);});},_De=0,_Df=function(_Dg,_Dh){var _Di=new T(function(){var _Dj=new T(function(){var _Dk=function(_Dl){var _Dm=new T(function(){var _Dn=new T(function(){return B(A(_Dh,[_Dl]));});return B(_CH(function(_Do){var _Dp=E(_Do);return (_Dp[0]==2)?(!B(_26(_Dp[1],_s9)))?[2]:E(_Dn):[2];}));}),_Dq=function(_Dr){return E(_Dm);};return [1,function(_Ds){return new F(function(){return A(_Bo,[_Ds,_Dq]);});}];};return B(A(_Dg,[_De,_Dk]));});return B(_CH(function(_Dt){var _Du=E(_Dt);return (_Du[0]==2)?(!B(_26(_Du[1],_s8)))?[2]:E(_Dj):[2];}));}),_Dv=function(_Dw){return E(_Di);};return function(_Dx){return new F(function(){return A(_Bo,[_Dx,_Dv]);});};},_Dy=function(_Dz,_DA){var _DB=function(_DC){var _DD=new T(function(){return B(A(_Dz,[_DC]));}),_DE=function(_DF){return new F(function(){return _rF(B(A(_DD,[_DF])),new T(function(){return [1,B(_Df(_DB,_DF))];}));});};return E(_DE);},_DG=new T(function(){return B(A(_Dz,[_DA]));}),_DH=function(_DI){return new F(function(){return _rF(B(A(_DG,[_DI])),new T(function(){return [1,B(_Df(_DB,_DI))];}));});};return E(_DH);},_DJ=function(_DK,_DL){return new F(function(){return A(_DL,[_2K]);});},_DM=[0,_2P,_DJ],_DN=[1,_DM,_3n],_DO=function(_DP,_DQ){return new F(function(){return A(_DQ,[_2M]);});},_DR=[0,_2O,_DO],_DS=[1,_DR,_DN],_DT=function(_DU,_DV,_DW){var _DX=E(_DU);if(!_DX[0]){return [2];}else{var _DY=E(_DX[1]),_DZ=_DY[1],_E0=new T(function(){return B(A(_DY[2],[_DV,_DW]));}),_E1=new T(function(){return B(_CH(function(_E2){var _E3=E(_E2);switch(_E3[0]){case 3:return (!B(_26(_DZ,_E3[1])))?[2]:E(_E0);case 4:return (!B(_26(_DZ,_E3[1])))?[2]:E(_E0);default:return [2];}}));}),_E4=function(_E5){return E(_E1);};return new F(function(){return _rF([1,function(_E6){return new F(function(){return A(_Bo,[_E6,_E4]);});}],new T(function(){return B(_DT(_DX[2],_DV,_DW));}));});}},_E7=function(_E8,_E9){return new F(function(){return _DT(_DS,_E8,_E9);});},_Ea=function(_Eb){var _Ec=function(_Ed){return [3,_Eb,_su];};return [1,function(_Ee){return new F(function(){return A(_Bo,[_Ee,_Ec]);});}];},_Ef=new T(function(){return B(A(_Dy,[_E7,_De,_Ea]));}),_Eg=new T(function(){return B(err(_ql));}),_Eh=new T(function(){return B(err(_qu));}),_Ei=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:50:3-15"));}),_Ej=[0,_6t,_6u,_3n,_Ei,_6t,_6t],_Ek=new T(function(){return B(_6r(_Ej));}),_El=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:51:3-15"));}),_Em=[0,_6t,_6u,_3n,_El,_6t,_6t],_En=new T(function(){return B(_6r(_Em));}),_Eo=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:52:3-14"));}),_Ep=[0,_6t,_6u,_3n,_Eo,_6t,_6t],_Eq=new T(function(){return B(_6r(_Ep));}),_Er=function(_Es,_Et){var _Eu=function(_Ev,_Ew){var _Ex=function(_Ey){return new F(function(){return A(_Ew,[new T(function(){return  -E(_Ey);})]);});},_Ez=new T(function(){return B(_CH(function(_EA){return new F(function(){return A(_Es,[_EA,_Ev,_Ex]);});}));}),_EB=function(_EC){return E(_Ez);},_ED=function(_EE){return new F(function(){return A(_Bo,[_EE,_EB]);});},_EF=new T(function(){return B(_CH(function(_EG){var _EH=E(_EG);if(_EH[0]==4){var _EI=E(_EH[1]);if(!_EI[0]){return new F(function(){return A(_Es,[_EH,_Ev,_Ew]);});}else{if(E(_EI[1])==45){if(!E(_EI[2])[0]){return [1,_ED];}else{return new F(function(){return A(_Es,[_EH,_Ev,_Ew]);});}}else{return new F(function(){return A(_Es,[_EH,_Ev,_Ew]);});}}}else{return new F(function(){return A(_Es,[_EH,_Ev,_Ew]);});}}));}),_EJ=function(_EK){return E(_EF);};return [1,function(_EL){return new F(function(){return A(_Bo,[_EL,_EJ]);});}];};return new F(function(){return _Dy(_Eu,_Et);});},_EM=new T(function(){return 1/0;}),_EN=function(_EO,_EP){return new F(function(){return A(_EP,[_EM]);});},_EQ=new T(function(){return 0/0;}),_ER=function(_ES,_ET){return new F(function(){return A(_ET,[_EQ]);});},_EU=new T(function(){return B(unCStr("NaN"));}),_EV=new T(function(){return B(unCStr("Infinity"));}),_EW=1024,_EX=-1021,_EY=new T(function(){return B(unCStr("GHC.Exception"));}),_EZ=new T(function(){return B(unCStr("base"));}),_F0=new T(function(){return B(unCStr("ArithException"));}),_F1=new T(function(){var _F2=hs_wordToWord64(4194982440),_F3=hs_wordToWord64(3110813675);return [0,_F2,_F3,[0,_F2,_F3,_EZ,_EY,_F0],_3n,_3n];}),_F4=function(_F5){return E(_F1);},_F6=function(_F7){var _F8=E(_F7);return new F(function(){return _50(B(_4Y(_F8[1])),_F4,_F8[2]);});},_F9=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_Fa=new T(function(){return B(unCStr("denormal"));}),_Fb=new T(function(){return B(unCStr("divide by zero"));}),_Fc=new T(function(){return B(unCStr("loss of precision"));}),_Fd=new T(function(){return B(unCStr("arithmetic underflow"));}),_Fe=new T(function(){return B(unCStr("arithmetic overflow"));}),_Ff=function(_Fg,_Fh){switch(E(_Fg)){case 0:return new F(function(){return _16(_Fe,_Fh);});break;case 1:return new F(function(){return _16(_Fd,_Fh);});break;case 2:return new F(function(){return _16(_Fc,_Fh);});break;case 3:return new F(function(){return _16(_Fb,_Fh);});break;case 4:return new F(function(){return _16(_Fa,_Fh);});break;default:return new F(function(){return _16(_F9,_Fh);});}},_Fi=function(_Fj){return new F(function(){return _Ff(_Fj,_3n);});},_Fk=function(_Fl,_Fm,_Fn){return new F(function(){return _Ff(_Fm,_Fn);});},_Fo=function(_Fp,_Fq){return new F(function(){return _6b(_Ff,_Fp,_Fq);});},_Fr=[0,_Fk,_Fi,_Fo],_Fs=new T(function(){return [0,_F4,_Fr,_Ft,_F6,_Fi];}),_Ft=function(_r5){return [0,_Fs,_r5];},_Fu=3,_Fv=new T(function(){return B(_Ft(_Fu));}),_Fw=new T(function(){return die(_Fv);}),_Fx=function(_Fy,_Fz){var _FA=E(_Fy);if(!_FA[0]){var _FB=_FA[1],_FC=E(_Fz);return (_FC[0]==0)?_FB==_FC[1]:(I_compareInt(_FC[1],_FB)==0)?true:false;}else{var _FD=_FA[1],_FE=E(_Fz);return (_FE[0]==0)?(I_compareInt(_FD,_FE[1])==0)?true:false:(I_compare(_FD,_FE[1])==0)?true:false;}},_FF=[0,0],_FG=function(_FH,_FI){while(1){var _FJ=E(_FH);if(!_FJ[0]){var _FK=E(_FJ[1]);if(_FK==(-2147483648)){_FH=[1,I_fromInt(-2147483648)];continue;}else{var _FL=E(_FI);if(!_FL[0]){return [0,_FK%_FL[1]];}else{_FH=[1,I_fromInt(_FK)];_FI=_FL;continue;}}}else{var _FM=_FJ[1],_FN=E(_FI);return (_FN[0]==0)?[1,I_rem(_FM,I_fromInt(_FN[1]))]:[1,I_rem(_FM,_FN[1])];}}},_FO=function(_FP,_FQ){if(!B(_Fx(_FQ,_FF))){return new F(function(){return _FG(_FP,_FQ);});}else{return E(_Fw);}},_FR=function(_FS,_FT){while(1){if(!B(_Fx(_FT,_FF))){var _FU=_FT,_FV=B(_FO(_FS,_FT));_FS=_FU;_FT=_FV;continue;}else{return E(_FS);}}},_FW=function(_FX){var _FY=E(_FX);if(!_FY[0]){var _FZ=E(_FY[1]);return (_FZ==(-2147483648))?E(_ux):(_FZ<0)?[0, -_FZ]:E(_FY);}else{var _G0=_FY[1];return (I_compareInt(_G0,0)>=0)?E(_FY):[1,I_negate(_G0)];}},_G1=function(_G2,_G3){while(1){var _G4=E(_G2);if(!_G4[0]){var _G5=E(_G4[1]);if(_G5==(-2147483648)){_G2=[1,I_fromInt(-2147483648)];continue;}else{var _G6=E(_G3);if(!_G6[0]){return [0,quot(_G5,_G6[1])];}else{_G2=[1,I_fromInt(_G5)];_G3=_G6;continue;}}}else{var _G7=_G4[1],_G8=E(_G3);return (_G8[0]==0)?[0,I_toInt(I_quot(_G7,I_fromInt(_G8[1])))]:[1,I_quot(_G7,_G8[1])];}}},_G9=5,_Ga=new T(function(){return B(_Ft(_G9));}),_Gb=new T(function(){return die(_Ga);}),_Gc=function(_Gd,_Ge){if(!B(_Fx(_Ge,_FF))){var _Gf=B(_FR(B(_FW(_Gd)),B(_FW(_Ge))));return (!B(_Fx(_Gf,_FF)))?[0,B(_G1(_Gd,_Gf)),B(_G1(_Ge,_Gf))]:E(_Fw);}else{return E(_Gb);}},_Gg=[0,1],_Gh=new T(function(){return B(unCStr("Negative exponent"));}),_Gi=new T(function(){return B(err(_Gh));}),_Gj=[0,2],_Gk=new T(function(){return B(_Fx(_Gj,_FF));}),_Gl=function(_Gm,_Gn){while(1){var _Go=E(_Gm);if(!_Go[0]){var _Gp=_Go[1],_Gq=E(_Gn);if(!_Gq[0]){var _Gr=_Gq[1],_Gs=subC(_Gp,_Gr);if(!E(_Gs[2])){return [0,_Gs[1]];}else{_Gm=[1,I_fromInt(_Gp)];_Gn=[1,I_fromInt(_Gr)];continue;}}else{_Gm=[1,I_fromInt(_Gp)];_Gn=_Gq;continue;}}else{var _Gt=E(_Gn);if(!_Gt[0]){_Gm=_Go;_Gn=[1,I_fromInt(_Gt[1])];continue;}else{return [1,I_sub(_Go[1],_Gt[1])];}}}},_Gu=function(_Gv,_Gw,_Gx){while(1){if(!E(_Gk)){if(!B(_Fx(B(_FG(_Gw,_Gj)),_FF))){if(!B(_Fx(_Gw,_Gg))){var _Gy=B(_uM(_Gv,_Gv)),_Gz=B(_G1(B(_Gl(_Gw,_Gg)),_Gj)),_GA=B(_uM(_Gv,_Gx));_Gv=_Gy;_Gw=_Gz;_Gx=_GA;continue;}else{return new F(function(){return _uM(_Gv,_Gx);});}}else{var _Gy=B(_uM(_Gv,_Gv)),_Gz=B(_G1(_Gw,_Gj));_Gv=_Gy;_Gw=_Gz;continue;}}else{return E(_Fw);}}},_GB=function(_GC,_GD){while(1){if(!E(_Gk)){if(!B(_Fx(B(_FG(_GD,_Gj)),_FF))){if(!B(_Fx(_GD,_Gg))){return new F(function(){return _Gu(B(_uM(_GC,_GC)),B(_G1(B(_Gl(_GD,_Gg)),_Gj)),_GC);});}else{return E(_GC);}}else{var _GE=B(_uM(_GC,_GC)),_GF=B(_G1(_GD,_Gj));_GC=_GE;_GD=_GF;continue;}}else{return E(_Fw);}}},_GG=function(_GH,_GI){if(!B(_jw(_GI,_FF))){if(!B(_Fx(_GI,_FF))){return new F(function(){return _GB(_GH,_GI);});}else{return E(_Gg);}}else{return E(_Gi);}},_GJ=[0,1],_GK=[0,0],_GL=[0,-1],_GM=function(_GN){var _GO=E(_GN);if(!_GO[0]){var _GP=_GO[1];return (_GP>=0)?(E(_GP)==0)?E(_GK):E(_um):E(_GL);}else{var _GQ=I_compareInt(_GO[1],0);return (_GQ<=0)?(E(_GQ)==0)?E(_GK):E(_GL):E(_um);}},_GR=function(_GS,_GT,_GU){while(1){var _GV=E(_GU);if(!_GV[0]){if(!B(_jw(_GS,_uZ))){return [0,B(_uM(_GT,B(_GG(_uC,_GS)))),_Gg];}else{var _GW=B(_GG(_uC,B(_uy(_GS))));return new F(function(){return _Gc(B(_uM(_GT,B(_GM(_GW)))),B(_FW(_GW)));});}}else{var _GX=B(_Gl(_GS,_GJ)),_GY=B(_uo(B(_uM(_GT,_uC)),B(_bz(E(_GV[1])))));_GS=_GX;_GT=_GY;_GU=_GV[2];continue;}}},_GZ=function(_H0,_H1){var _H2=E(_H0);if(!_H2[0]){var _H3=_H2[1],_H4=E(_H1);return (_H4[0]==0)?_H3>=_H4[1]:I_compareInt(_H4[1],_H3)<=0;}else{var _H5=_H2[1],_H6=E(_H1);return (_H6[0]==0)?I_compareInt(_H5,_H6[1])>=0:I_compare(_H5,_H6[1])>=0;}},_H7=function(_H8){var _H9=E(_H8);if(!_H9[0]){var _Ha=_H9[2];return new F(function(){return _Gc(B(_uM(B(_v0(new T(function(){return B(_bz(E(_H9[1])));}),new T(function(){return B(_uD(_Ha,0));},1),B(_1A(_uI,_Ha)))),_GJ)),_GJ);});}else{var _Hb=_H9[1],_Hc=_H9[3],_Hd=E(_H9[2]);if(!_Hd[0]){var _He=E(_Hc);if(!_He[0]){return new F(function(){return _Gc(B(_uM(B(_vg(_uC,_Hb)),_GJ)),_GJ);});}else{var _Hf=_He[1];if(!B(_GZ(_Hf,_uZ))){var _Hg=B(_GG(_uC,B(_uy(_Hf))));return new F(function(){return _Gc(B(_uM(B(_vg(_uC,_Hb)),B(_GM(_Hg)))),B(_FW(_Hg)));});}else{return new F(function(){return _Gc(B(_uM(B(_uM(B(_vg(_uC,_Hb)),B(_GG(_uC,_Hf)))),_GJ)),_GJ);});}}}else{var _Hh=_Hd[1],_Hi=E(_Hc);if(!_Hi[0]){return new F(function(){return _GR(_uZ,B(_vg(_uC,_Hb)),_Hh);});}else{return new F(function(){return _GR(_Hi[1],B(_vg(_uC,_Hb)),_Hh);});}}}},_Hj=function(_Hk,_Hl){while(1){var _Hm=E(_Hl);if(!_Hm[0]){return [0];}else{if(!B(A(_Hk,[_Hm[1]]))){return E(_Hm);}else{_Hl=_Hm[2];continue;}}}},_Hn=function(_Ho,_Hp){var _Hq=E(_Ho);if(!_Hq[0]){var _Hr=_Hq[1],_Hs=E(_Hp);return (_Hs[0]==0)?_Hr>_Hs[1]:I_compareInt(_Hs[1],_Hr)<0;}else{var _Ht=_Hq[1],_Hu=E(_Hp);return (_Hu[0]==0)?I_compareInt(_Ht,_Hu[1])>0:I_compare(_Ht,_Hu[1])>0;}},_Hv=0,_Hw=function(_Hx,_Hy){return E(_Hx)==E(_Hy);},_Hz=function(_HA){return new F(function(){return _Hw(_Hv,_HA);});},_HB=[0,E(_uZ),E(_Gg)],_HC=[1,_HB],_HD=[0,-2147483648],_HE=[0,2147483647],_HF=function(_HG,_HH,_HI){var _HJ=E(_HI);if(!_HJ[0]){return [1,new T(function(){var _HK=B(_H7(_HJ));return [0,E(_HK[1]),E(_HK[2])];})];}else{var _HL=E(_HJ[3]);if(!_HL[0]){return [1,new T(function(){var _HM=B(_H7(_HJ));return [0,E(_HM[1]),E(_HM[2])];})];}else{var _HN=_HL[1];if(!B(_Hn(_HN,_HE))){if(!B(_jw(_HN,_HD))){var _HO=function(_HP){var _HQ=_HP+B(_w5(_HN))|0;return (_HQ<=(E(_HH)+3|0))?(_HQ>=(E(_HG)-3|0))?[1,new T(function(){var _HR=B(_H7(_HJ));return [0,E(_HR[1]),E(_HR[2])];})]:E(_HC):[0];},_HS=B(_Hj(_Hz,_HJ[1]));if(!_HS[0]){var _HT=E(_HJ[2]);if(!_HT[0]){return E(_HC);}else{var _HU=B(_r6(_Hz,_HT[1]));if(!E(_HU[2])[0]){return E(_HC);}else{return new F(function(){return _HO( -B(_uD(_HU[1],0)));});}}}else{return new F(function(){return _HO(B(_uD(_HS,0)));});}}else{return [0];}}else{return [0];}}}},_HV=function(_HW,_HX){return [2];},_HY=[0,1],_HZ=function(_I0,_I1){var _I2=E(_I0);if(!_I2[0]){var _I3=_I2[1],_I4=E(_I1);if(!_I4[0]){var _I5=_I4[1];return (_I3!=_I5)?(_I3>_I5)?2:0:1;}else{var _I6=I_compareInt(_I4[1],_I3);return (_I6<=0)?(_I6>=0)?1:2:0;}}else{var _I7=_I2[1],_I8=E(_I1);if(!_I8[0]){var _I9=I_compareInt(_I7,_I8[1]);return (_I9>=0)?(_I9<=0)?1:2:0;}else{var _Ia=I_compare(_I7,_I8[1]);return (_Ia>=0)?(_Ia<=0)?1:2:0;}}},_Ib=function(_Ic,_Id){var _Ie=E(_Ic);return (_Ie[0]==0)?_Ie[1]*Math.pow(2,_Id):I_toNumber(_Ie[1])*Math.pow(2,_Id);},_If=function(_Ig,_Ih){while(1){var _Ii=E(_Ig);if(!_Ii[0]){var _Ij=E(_Ii[1]);if(_Ij==(-2147483648)){_Ig=[1,I_fromInt(-2147483648)];continue;}else{var _Ik=E(_Ih);if(!_Ik[0]){var _Il=_Ik[1];return [0,[0,quot(_Ij,_Il)],[0,_Ij%_Il]];}else{_Ig=[1,I_fromInt(_Ij)];_Ih=_Ik;continue;}}}else{var _Im=E(_Ih);if(!_Im[0]){_Ig=_Ii;_Ih=[1,I_fromInt(_Im[1])];continue;}else{var _In=I_quotRem(_Ii[1],_Im[1]);return [0,[1,_In[1]],[1,_In[2]]];}}}},_Io=[0,0],_Ip=function(_Iq,_Ir,_Is){if(!B(_Fx(_Is,_Io))){var _It=B(_If(_Ir,_Is)),_Iu=_It[1];switch(B(_HZ(B(_cz(_It[2],1)),_Is))){case 0:return new F(function(){return _Ib(_Iu,_Iq);});break;case 1:if(!(B(_w5(_Iu))&1)){return new F(function(){return _Ib(_Iu,_Iq);});}else{return new F(function(){return _Ib(B(_uo(_Iu,_HY)),_Iq);});}break;default:return new F(function(){return _Ib(B(_uo(_Iu,_HY)),_Iq);});}}else{return E(_Fw);}},_Iv=function(_Iw){var _Ix=_um,_Iy=0;while(1){if(!B(_jw(_Ix,_Iw))){if(!B(_Hn(_Ix,_Iw))){if(!B(_Fx(_Ix,_Iw))){return new F(function(){return _rs("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_Iy);}}else{return _Iy-1|0;}}else{var _Iz=B(_cz(_Ix,1)),_IA=_Iy+1|0;_Ix=_Iz;_Iy=_IA;continue;}}},_IB=function(_IC){var _ID=E(_IC);if(!_ID[0]){var _IE=_ID[1]>>>0;if(!_IE){return -1;}else{var _IF=1,_IG=0;while(1){if(_IF>=_IE){if(_IF<=_IE){if(_IF!=_IE){return new F(function(){return _rs("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_IG);}}else{return _IG-1|0;}}else{var _IH=imul(_IF,2)>>>0,_II=_IG+1|0;_IF=_IH;_IG=_II;continue;}}}}else{return new F(function(){return _Iv(_ID);});}},_IJ=function(_IK){var _IL=E(_IK);if(!_IL[0]){var _IM=_IL[1]>>>0;if(!_IM){return [0,-1,0];}else{var _IN=function(_IO,_IP){while(1){if(_IO>=_IM){if(_IO<=_IM){if(_IO!=_IM){return new F(function(){return _rs("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_IP);}}else{return _IP-1|0;}}else{var _IQ=imul(_IO,2)>>>0,_IR=_IP+1|0;_IO=_IQ;_IP=_IR;continue;}}};return [0,B(_IN(1,0)),(_IM&_IM-1>>>0)>>>0&4294967295];}}else{var _IS=B(_IB(_IL)),_IT=_IS>>>0;if(!_IT){var _IU=E(_IS);return (_IU==(-2))?[0,-2,0]:[0,_IU,1];}else{var _IV=function(_IW,_IX){while(1){if(_IW>=_IT){if(_IW<=_IT){if(_IW!=_IT){return new F(function(){return _rs("GHCIntegerType.lhs:(610,5)-(612,40)|function l2");});}else{return E(_IX);}}else{return _IX-1|0;}}else{var _IY=imul(_IW,2)>>>0,_IZ=_IX+1|0;_IW=_IY;_IX=_IZ;continue;}}},_J0=B(_IV(1,0));return ((_J0+_J0|0)!=_IS)?[0,_IS,1]:[0,_IS,0];}}},_J1=function(_J2,_J3){while(1){var _J4=E(_J2);if(!_J4[0]){var _J5=_J4[1],_J6=E(_J3);if(!_J6[0]){return [0,(_J5>>>0&_J6[1]>>>0)>>>0&4294967295];}else{_J2=[1,I_fromInt(_J5)];_J3=_J6;continue;}}else{var _J7=E(_J3);if(!_J7[0]){_J2=_J4;_J3=[1,I_fromInt(_J7[1])];continue;}else{return [1,I_and(_J4[1],_J7[1])];}}}},_J8=[0,2],_J9=function(_Ja,_Jb){var _Jc=E(_Ja);if(!_Jc[0]){var _Jd=(_Jc[1]>>>0&(2<<_Jb>>>0)-1>>>0)>>>0,_Je=1<<_Jb>>>0;return (_Je<=_Jd)?(_Je>=_Jd)?1:2:0;}else{var _Jf=B(_J1(_Jc,B(_Gl(B(_cz(_J8,_Jb)),_um)))),_Jg=B(_cz(_um,_Jb));return (!B(_Hn(_Jg,_Jf)))?(!B(_jw(_Jg,_Jf)))?1:2:0;}},_Jh=function(_Ji,_Jj){while(1){var _Jk=E(_Ji);if(!_Jk[0]){_Ji=[1,I_fromInt(_Jk[1])];continue;}else{return [1,I_shiftRight(_Jk[1],_Jj)];}}},_Jl=function(_Jm,_Jn,_Jo,_Jp){var _Jq=B(_IJ(_Jp)),_Jr=_Jq[1];if(!E(_Jq[2])){var _Js=B(_IB(_Jo));if(_Js<((_Jr+_Jm|0)-1|0)){var _Jt=_Jr+(_Jm-_Jn|0)|0;if(_Jt>0){if(_Jt>_Js){if(_Jt<=(_Js+1|0)){if(!E(B(_IJ(_Jo))[2])){return 0;}else{return new F(function(){return _Ib(_HY,_Jm-_Jn|0);});}}else{return 0;}}else{var _Ju=B(_Jh(_Jo,_Jt));switch(B(_J9(_Jo,_Jt-1|0))){case 0:return new F(function(){return _Ib(_Ju,_Jm-_Jn|0);});break;case 1:if(!(B(_w5(_Ju))&1)){return new F(function(){return _Ib(_Ju,_Jm-_Jn|0);});}else{return new F(function(){return _Ib(B(_uo(_Ju,_HY)),_Jm-_Jn|0);});}break;default:return new F(function(){return _Ib(B(_uo(_Ju,_HY)),_Jm-_Jn|0);});}}}else{return new F(function(){return _Ib(_Jo,(_Jm-_Jn|0)-_Jt|0);});}}else{if(_Js>=_Jn){var _Jv=B(_Jh(_Jo,(_Js+1|0)-_Jn|0));switch(B(_J9(_Jo,_Js-_Jn|0))){case 0:return new F(function(){return _Ib(_Jv,((_Js-_Jr|0)+1|0)-_Jn|0);});break;case 2:return new F(function(){return _Ib(B(_uo(_Jv,_HY)),((_Js-_Jr|0)+1|0)-_Jn|0);});break;default:if(!(B(_w5(_Jv))&1)){return new F(function(){return _Ib(_Jv,((_Js-_Jr|0)+1|0)-_Jn|0);});}else{return new F(function(){return _Ib(B(_uo(_Jv,_HY)),((_Js-_Jr|0)+1|0)-_Jn|0);});}}}else{return new F(function(){return _Ib(_Jo, -_Jr);});}}}else{var _Jw=B(_IB(_Jo))-_Jr|0,_Jx=function(_Jy){var _Jz=function(_JA,_JB){if(!B(_w8(B(_cz(_JB,_Jn)),_JA))){return new F(function(){return _Ip(_Jy-_Jn|0,_JA,_JB);});}else{return new F(function(){return _Ip((_Jy-_Jn|0)+1|0,_JA,B(_cz(_JB,1)));});}};if(_Jy>=_Jn){if(_Jy!=_Jn){return new F(function(){return _Jz(_Jo,new T(function(){return B(_cz(_Jp,_Jy-_Jn|0));}));});}else{return new F(function(){return _Jz(_Jo,_Jp);});}}else{return new F(function(){return _Jz(new T(function(){return B(_cz(_Jo,_Jn-_Jy|0));}),_Jp);});}};if(_Jm>_Jw){return new F(function(){return _Jx(_Jm);});}else{return new F(function(){return _Jx(_Jw);});}}},_JC=new T(function(){return 0/0;}),_JD=new T(function(){return -1/0;}),_JE=new T(function(){return 1/0;}),_JF=0,_JG=function(_JH,_JI){if(!B(_Fx(_JI,_Io))){if(!B(_Fx(_JH,_Io))){if(!B(_jw(_JH,_Io))){return new F(function(){return _Jl(-1021,53,_JH,_JI);});}else{return  -B(_Jl(-1021,53,B(_uy(_JH)),_JI));}}else{return E(_JF);}}else{return (!B(_Fx(_JH,_Io)))?(!B(_jw(_JH,_Io)))?E(_JE):E(_JD):E(_JC);}},_JJ=function(_JK){var _JL=E(_JK);switch(_JL[0]){case 3:var _JM=_JL[1];return (!B(_26(_JM,_EV)))?(!B(_26(_JM,_EU)))?E(_HV):E(_ER):E(_EN);case 5:var _JN=B(_HF(_EX,_EW,_JL[1]));if(!_JN[0]){return E(_EN);}else{var _JO=new T(function(){var _JP=E(_JN[1]);return B(_JG(_JP[1],_JP[2]));});return function(_JQ,_JR){return new F(function(){return A(_JR,[_JO]);});};}break;default:return E(_HV);}},_JS=new T(function(){return B(A(_Er,[_JJ,_De,_Ea]));}),_JT=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:53:3-11"));}),_JU=[0,_6t,_6u,_3n,_JT,_6t,_6t],_JV=new T(function(){return B(_6r(_JU));}),_JW=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:62:3-10"));}),_JX=[0,_6t,_6u,_3n,_JW,_6t,_6t],_JY=new T(function(){return B(_6r(_JX));}),_JZ=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:63:3-11"));}),_K0=[0,_6t,_6u,_3n,_JZ,_6t,_6t],_K1=new T(function(){return B(_6r(_K0));}),_K2=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:72:3-12"));}),_K3=[0,_6t,_6u,_3n,_K2,_6t,_6t],_K4=new T(function(){return B(_6r(_K3));}),_K5=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:73:3-12"));}),_K6=[0,_6t,_6u,_3n,_K5,_6t,_6t],_K7=new T(function(){return B(_6r(_K6));}),_K8=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:74:3-11"));}),_K9=[0,_6t,_6u,_3n,_K8,_6t,_6t],_Ka=new T(function(){return B(_6r(_K9));}),_Kb=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:89:3-14"));}),_Kc=[0,_6t,_6u,_3n,_Kb,_6t,_6t],_Kd=new T(function(){return B(_6r(_Kc));}),_Ke=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:90:3-11"));}),_Kf=[0,_6t,_6u,_3n,_Ke,_6t,_6t],_Kg=new T(function(){return B(_6r(_Kf));}),_Kh=new T(function(){return B(unCStr("input[name=\'mount\']:checked"));}),_Ki="offset",_Kj="bottom",_Kk="top",_Kl=function(_Km){while(1){var _Kn=B((function(_Ko){var _Kp=E(_Ko);if(!_Kp[0]){return [0];}else{var _Kq=_Kp[2],_Kr=E(_Kp[1]);if(!E(_Kr[2])[0]){return [1,_Kr[1],new T(function(){return B(_Kl(_Kq));})];}else{_Km=_Kq;return null;}}})(_Km));if(_Kn!=null){return _Kn;}}},_Ks=function(_Kt,_Ku){return [1,new T(function(){var _Kv=B(_Kl(B(_rv(_JS,_Kt))));if(!_Kv[0]){return E(_Eg);}else{if(!E(_Kv[2])[0]){return E(_Kv[1])*1.7453292519943295e-2;}else{return E(_Eh);}}}),_Ku];},_Kw="rotations",_Kx=new T(function(){return B(unCStr("loadPath"));}),_Ky=function(_Kz,_){var _KA=function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);},_KB=E(_KA)("processDump",toJSStr(_Kx));return new F(function(){return _dQ(_);});},_KC=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:121:5-17"));}),_KD=[0,_6t,_6u,_3n,_KC,_6t,_6t],_KE=new T(function(){return B(_6r(_KD));}),_KF=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:124:5-19"));}),_KG=[0,_6t,_6u,_3n,_KF,_6t,_6t],_KH=new T(function(){return B(_6r(_KG));}),_KI=new T(function(){return B(unCStr(".txt"));}),_KJ=new T(function(){return B(unCStr("download"));}),_KK=function(_KL,_KM){var _KN=E(_KM);if(!_KN[0]){return [0,_3n,_3n];}else{var _KO=_KN[1];if(!B(A(_KL,[_KO]))){var _KP=new T(function(){var _KQ=B(_KK(_KL,_KN[2]));return [0,_KQ[1],_KQ[2]];});return [0,[1,_KO,new T(function(){return E(E(_KP)[1]);})],new T(function(){return E(E(_KP)[2]);})];}else{return [0,_3n,_KN];}}},_KR=function(_KS){var _KT=_KS>>>0;if(_KT>887){var _KU=u_iswspace(_KS);return (E(_KU)==0)?false:true;}else{var _KV=E(_KT);return (_KV==32)?true:(_KV-9>>>0>4)?(E(_KV)==160)?true:false:true;}},_KW=function(_KX){return new F(function(){return _KR(E(_KX));});},_KY=function(_KZ,_L0,_L1){var _L2=function(_L3){var _L4=B(_Hj(_KW,_L3));if(!_L4[0]){return E(_L0);}else{var _L5=new T(function(){var _L6=B(_KK(_KW,_L4));return [0,_L6[1],_L6[2]];});return new F(function(){return A(_KZ,[new T(function(){return E(E(_L5)[1]);}),new T(function(){return B(_L2(E(_L5)[2]));})]);});}};return new F(function(){return _L2(_L1);});},_L7=function(_){var _L8=B(A(_fn,[_6B,_qt,_])),_L9=E(_L8);if(!_L9[0]){return new F(function(){return die(_Ek);});}else{var _La=B(A(_fn,[_6B,_qs,_])),_Lb=E(_La);if(!_Lb[0]){return new F(function(){return die(_En);});}else{var _Lc=B(A(_fn,[_6B,_iQ,_])),_Ld=E(_Lc);if(!_Ld[0]){return new F(function(){return die(_Eq);});}else{var _Le=_Ld[1],_Lf=B(A(_fn,[_6B,_Kw,_])),_Lg=E(_Lf);if(!_Lg[0]){return new F(function(){return die(_JV);});}else{var _Lh=_Lg[1],_Li=nMV(_qc),_Lj=_Li,_Lk=nMV(_qk),_Ll=_Lk,_Lm=B(A(_5,[_6B,_qr,_])),_Ln=nMV(_Lm),_Lo=_Ln,_Lp=nMV(_qr),_Lq=_Lp,_Lr=B(A(_fn,[_6B,_ja,_])),_Ls=E(_Lr);if(!_Ls[0]){return new F(function(){return die(_JY);});}else{var _Lt=E(_Ls[1]),_Lu=E(_N),_Lv=_Lu(_Lt);if(!_Lv){return new F(function(){return die(_JY);});}else{var _Lw=E(_M),_Lx=_Lw(_Lt),_Ly=_Lx,_Lz=B(A(_fn,[_6B,_j6,_])),_LA=function(_,_LB){var _LC=E(_LB);if(!_LC[0]){return new F(function(){return die(_K1);});}else{var _LD=function(_){return new F(function(){return _mm(_Ll,_Lj,_Lo,_);});},_LE=B(_o7(_Lj,[0,_Ly,_Lt],_LD,_)),_LF=B(_pk(_Ll,_LC[1],_LD,_)),_LG=function(_LH,_){var _LI=String(E(_LH)),_LJ=jsParseJSON(_LI);if(!_LJ[0]){return _8P;}else{var _LK=B(_4e(_LJ[1]));if(!_LK[0]){return _8P;}else{var _LL=_LK[1],_=wMV(_Lj,new T(function(){return E(E(_LL)[1]);})),_=wMV(_Ll,new T(function(){return E(E(_LL)[2]);}));return _8P;}}},_LM=__createJSFunc(2,E(_LG)),_LN=(function(s,f){Haste[s] = f;}),_LO=E(_LN)("processDump",_LM),_LP=B(A(_fn,[_6B,_Kk,_])),_LQ=E(_LP);if(!_LQ[0]){return new F(function(){return die(_K4);});}else{var _LR=_LQ[1],_LS=B(A(_fn,[_6B,_Kj,_])),_LT=E(_LS);if(!_LT[0]){return new F(function(){return die(_K7);});}else{var _LU=_LT[1],_LV=B(A(_fn,[_6B,_Ki,_])),_LW=E(_LV);if(!_LW[0]){return new F(function(){return die(_Ka);});}else{var _LX=_LW[1],_LY=B(A(_pR,[_6B,_pI,_qq,_])),_LZ=function(_M0,_){var _M1=E(_M0),_M2=toJSStr(_qp),_M3=E(_pX)(_M2),_M4=B(A(_5,[_6B,new T(function(){var _M5=String(_M3);return fromJSStr(_M5);}),_])),_=wMV(_Lo,_M4),_M6=E(_pY)(_M2),_M7=new T(function(){var _M8=String(_M6);return fromJSStr(_M8);}),_=wMV(_Lq,_M7),_M9=B(A(_fn,[_6B,_qo,_])),_Ma=E(_M9);if(!_Ma[0]){return new F(function(){return die(_KE);});}else{var _Mb=toJSStr(E(_KJ)),_Mc=E(_9t),_Md=_Mc(E(_Ma[1]),_Mb,toJSStr(B(_16(_M7,_qn)))),_Me=B(A(_fn,[_6B,_iN,_])),_Mf=E(_Me);if(!_Mf[0]){return new F(function(){return die(_KH);});}else{var _Mg=_Mc(E(_Mf[1]),_Mb,toJSStr(B(_16(_M7,_KI))));return new F(function(){return _mm(_Ll,_Lj,_Lo,_);});}}},_Mh=B(A(_c2,[_6C,_S,_o,_L9[1],_b4,_LZ,_])),_Mi=B(A(_c2,[_6C,_S,_o,_Lb[1],_b4,_Ky,_])),_Mj=function(_){var _Mk=B(A(_fn,[_6B,_iQ,_])),_Ml=E(_Mk);if(!_Ml[0]){return new F(function(){return die(_Kd);});}else{var _Mm=B(A(_fn,[_6B,_Kw,_])),_Mn=E(_Mm);if(!_Mn[0]){return new F(function(){return die(_Kg);});}else{var _Mo=B(A(_lQ,[_S,_6B,_Ml[1],_iP,_])),_Mp=rMV(_Ll),_Mq=E(_Mp),_=wMV(_Ll,[0,_Mq[1],_Mq[2],_Mo,_Mq[4],_Mq[5],_Mq[6],_Mq[7],_Mq[8]]),_Mr=B(A(_lQ,[_S,_6B,_Mn[1],_iP,_])),_Ms=rMV(_Ll),_Mt=E(_Ms),_=wMV(_Ll,[0,_Mt[1],_Mt[2],_Mt[3],_Mt[4],_Mt[5],_Mt[6],_Mt[7],new T(function(){return B(_KY(_Ks,_3n,_Mr));})]),_Mu=B(A(_fn,[_6B,_Kk,_])),_Mv=B(A(_lQ,[_S,_6B,new T(function(){return B(_q1(_Mu));}),_iP,_])),_Mw=B(A(_fn,[_6B,_Kj,_])),_Mx=B(A(_lQ,[_S,_6B,new T(function(){return B(_q1(_Mw));}),_iP,_])),_My=B(A(_fn,[_6B,_Ki,_])),_Mz=B(A(_lQ,[_S,_6B,new T(function(){return B(_q1(_My));}),_iP,_])),_MA=B(A(_pR,[_6B,_pI,_Kh,_])),_MB=E(_MA);if(!_MB[0]){return new F(function(){return _nw(_);});}else{if(!E(_MB[2])[0]){var _MC=B(A(_lQ,[_S,_6B,_MB[1],_iP,_])),_MD=rMV(_Ll),_ME=E(_MD),_=wMV(_Ll,[0,_ME[1],_ME[2],_ME[3],new T(function(){var _MF=B(_Kl(B(_rv(_JS,_Mv))));if(!_MF[0]){return E(_Eg);}else{if(!E(_MF[2])[0]){return E(_MF[1]);}else{return E(_Eh);}}}),new T(function(){var _MG=B(_Kl(B(_rv(_JS,_Mx))));if(!_MG[0]){return E(_Eg);}else{if(!E(_MG[2])[0]){return E(_MG[1]);}else{return E(_Eh);}}}),new T(function(){var _MH=B(_Kl(B(_rv(_JS,_Mz))));if(!_MH[0]){return E(_Eg);}else{if(!E(_MH[2])[0]){return E(_MH[1]);}else{return E(_Eh);}}}),new T(function(){var _MI=B(_Kl(B(_rv(_Ef,_MC))));if(!_MI[0]){return E(_qm);}else{if(!E(_MI[2])[0]){return E(_MI[1]);}else{return E(_qv);}}}),_ME[8]]);return new F(function(){return _mm(_Ll,_Lj,_Lo,_);});}else{return new F(function(){return _nw(_);});}}}}},_MJ=function(_MK,_){return new F(function(){return _Mj(_);});},_ML=function(_MM,_){while(1){var _MN=E(_MM);if(!_MN[0]){var _MO=B(A(_c2,[_6C,_S,_o,_Le,_b4,_MJ,_])),_MP=B(A(_c2,[_6C,_S,_o,_Lh,_b4,_MJ,_])),_MQ=B(A(_c2,[_6C,_S,_o,_LR,_b4,_MJ,_])),_MR=B(A(_c2,[_6C,_S,_o,_LU,_b4,_MJ,_])),_MS=B(A(_c2,[_6C,_S,_o,_LX,_b4,_MJ,_]));return _a;}else{var _MT=B(A(_c2,[_6C,_S,_o,_MN[1],_b4,_MJ,_]));_MM=_MN[2];continue;}}},_MU=B(_ML(_LY,_)),_MV=B(A(_c2,[_6C,_S,_L,_Le,_nx,_MJ,_])),_MW=B(A(_c2,[_6C,_S,_L,_Lh,_nx,_MJ,_])),_MX=B(A(_c2,[_6C,_S,_L,_LR,_nx,_MJ,_])),_MY=B(A(_c2,[_6C,_S,_L,_LU,_nx,_MJ,_])),_MZ=B(A(_c2,[_6C,_S,_L,_LX,_nx,_MJ,_]));return new F(function(){return _mm(_Ll,_Lj,_Lo,_);});}}}}},_N0=E(_Lz);if(!_N0[0]){return new F(function(){return _LA(_,_6t);});}else{var _N1=E(_N0[1]),_N2=_Lu(_N1);if(!_N2){return new F(function(){return _LA(_,_6t);});}else{var _N3=_Lw(_N1);return new F(function(){return _LA(_,[1,[0,_N3,_N1]]);});}}}}}}}}},_N4=function(_){return new F(function(){return _L7(_);});};
var hasteMain = function() {B(A(_N4, [0]));};window.onload = hasteMain;