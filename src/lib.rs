//! Provides implementations of high-accuracy projectively-extended rational numbers
//!
//! Projectively-extended rationals differ from normal rationals because they have
//! a single, signless infinity and a single, signless zero. This means that `1/0`
//! can be defined as equal to `∞` and `1/∞` equal to `0`.
//!
//! # Infinity
//!
//! For unsigned numbers, `∞` is greater than every number, whereas with signed numbers,
//! `∞` is not comparable to any number but itself. This is because `∞` equals `-∞` so no
//! ordering can exist.
//!
//! # NaN
//!
//! `∞ + ∞`, `∞ - ∞`, `∞ * 0`, `0 * ∞`, `∞ / ∞`, and `0 / 0` are all `NaN`
//!
//! A value of `NaN` in any operation always returns `NaN`. `NaN` is not ordered and
//! is not equal to any number, including itself.

use std::*;
use std::cmp::*;
use std::ops::*;

macro_rules! try_or {
    (continue $x: expr) => {
        match $x {
            Some(x) => x,
            None => continue,
        }
    };
    (return $x: expr) => {
        match $x {
            Some(x) => x,
            None => return None,
        }
    };
}

macro_rules! impl_u_from {
    ($($t: ty)+) => {
        $(
            impl From<$t> for URational {
                fn from(n: $t) -> URational {
                    URational::new(n as u64, 1)
                }
            }
            impl From<$t> for Rational {
                fn from(n: $t) -> Rational {
                    Rational::from(URational::from(n))
                }
            }
        )+
    }
}

macro_rules! impl_to {
    ($($t: ty)+) => {
        $(
            impl From<URational> for $t {
                fn from(r: URational) -> $t {
                    (r.numerator as $t) / (r.denominator as $t)
                }
            }
            impl From<Rational> for $t {
                fn from(r: Rational) -> $t {
                    (if r.negative { -1.0 } else { 1.0 }) * (r.unsigned.numerator as $t) / (r.unsigned.denominator as $t)
                }
            }
        )+
    }
}

macro_rules! impl_from {
    ($($t: ty)+) => {
        $(
            impl From<$t> for Rational {
                fn from(n: $t) -> Rational {
                    Rational::new(n as i64, 1)
                }
            }
        )+
    }
}

macro_rules! impl_ops {
    ($rational: ident; $assign: ident $non: ident, $assign_name: ident $non_name: ident, $f: ident $($b: expr)*) => {
        impl $assign for $rational {
            #[inline]
            fn $assign_name(&mut self, mut other: $rational) {
                self.$f(&mut other $(, $b)*);
            }
        }
        impl $non for $rational {
            type Output = $rational;

            #[inline]
            fn $non_name(self, mut other: $rational) -> $rational {
                let mut r = self;
                r.$f(&mut other$(, $b)*);
                r
            }
        }
    }
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let c = b;
        b = a % b;
        a = c;
    }
    a
}

/// A type representing an unsigned projectively-extended rational number
///
/// Subtracting a large number from a smaller one always returns `0` unless
/// the smaller number is `∞`.
///
/// # Example
///
/// ```
/// use extended_rational::URational;
///
/// let a = URational::new(3, 17);
/// let b = URational::new(4, 7);
///
/// assert_eq!(a+b, URational::new(89, 119));
/// ```
#[derive(Copy, Clone)]
pub struct URational {
    numerator: u64,
    denominator: u64,
}

impl URational {
    /// Create a new unsigned rational with the given numerator and denominator
    pub fn new(numerator: u64, denominator: u64) -> URational {
        let mut r = URational {
            numerator,
            denominator,
        };
        r.simplify();
        r
    }

    /// Returns the numerator of this rational
    #[inline(always)] pub fn numerator(&self) -> u64 { self.numerator }

    /// Returns the denominator of this rational
    #[inline(always)] pub fn denominator(&self) -> u64 { self.denominator }

    /// Returns the reciprocal of this rational
    #[inline] pub fn reciprocal(&self) -> URational { URational { numerator: self.denominator, denominator: self.numerator } }

    /// Returns the complexity of this rational (max of numerator and denominator)
    #[inline] pub fn complexity(&self) -> u64 { max(self.numerator, self.denominator) }

    /// Returns the smallest value an unsigned rational can store
    #[inline(always)] pub fn min_value() -> URational { URational { numerator: 0, denominator: 1 } }

    /// Returns the smallest non-zero value an unsigned rational can store
    #[inline(always)] pub fn min_pos_value() -> URational { URational { numerator: 1, denominator: u64::MAX } }

    /// Returns the largest value an unsigned rational can store
    #[inline(always)] pub fn max_value() -> URational { URational { numerator: u64::MAX, denominator: 1 } }

    /// Returns an unsigned rational representing `NaN`
    #[inline(always)] pub fn nan() -> URational { URational { numerator: 0, denominator: 0 } }

    /// Returns an unsigned rational representing `0`
    #[inline(always)] pub fn zero() -> URational { URational { numerator: 0, denominator: 1 } }

    /// Returns an unsigned rational representing `∞`
    #[inline(always)] pub fn infinity() -> URational { URational { numerator: 1, denominator: 0 } }

    /// Returns an unsigned rational representing `1`
    #[inline(always)] pub fn one() -> URational { URational { numerator: 1, denominator: 1 } }

    /// Returns `true` if this rational is `NaN` and `false` otherwise
    #[inline] pub fn is_nan(&self) -> bool { self.numerator == 0 && self.denominator == 0 }

    /// Returns `true` if this rational is `0` and `false` otherwise
    #[inline] pub fn is_zero(&self) -> bool { self.numerator == 0 && self.denominator != 0 }

    /// Returns `true` if this rational is `∞` and `false` otherwise
    #[inline] pub fn is_infinity(&self) -> bool { self.numerator != 0 && self.denominator == 0 }

    /// Returns `true` if this rational is a signed number (not `NaN`, `0`, or `∞`) and `false` otherwise
    #[inline] pub fn is_signed(&self) -> bool { self.numerator != 0 && self.denominator != 0 }

    /// Returns this rational with no fractional component by rounding down
    pub fn floor(&self) -> URational {
        if self.denominator != 0 {
            URational {
                numerator: self.numerator / self.denominator,
                denominator: 1,
            }
        } else {
            *self
        }
    }

    /// Returns this rational with no fractional component by rounding
    pub fn round(&self) -> URational {
        if self.denominator != 0 {
            if (self.numerator % self.denominator) > self.denominator/2 {
                URational {
                    numerator: (self.numerator / self.denominator) + 1,
                    denominator: 1,
                }
            } else {
                URational {
                    numerator: self.numerator / self.denominator,
                    denominator: 1,
                }
            }
        } else {
            *self
        }
    }

    /// Returns this rational with no fractional component by rounding up
    pub fn ceil(&self) -> URational {
        if self.denominator != 0 {
            if (self.numerator % self.denominator) != 0 {
                URational {
                    numerator: (self.numerator / self.denominator) + 1,
                    denominator: 1,
                }
            } else {
                URational {
                    numerator: self.numerator / self.denominator,
                    denominator: 1,
                }
            }
        } else {
            *self
        }
    }

    fn simplify(&mut self) {
        let common = gcd(self.numerator, self.denominator);
        if common > 1 {
            self.numerator /= common;
            self.denominator /= common;
        }
    }

    fn shift(&mut self) {
        let shift_partial = |a: &mut u64| {
            if *a & 1 == 1 {
                *a >>= 1;
                *a += 1;
            } else {
                *a >>= 1;
            }
        };
        shift_partial(&mut self.numerator);
        shift_partial(&mut self.denominator);
        self.simplify();
    }

    fn add_sub(&mut self, other: &mut URational, sub: bool) {
        if sub && other > self && !other.is_infinity() {
            *self = URational::zero();
            return;
        }
        let mut first = true;
        loop {
            if first {
                first = false;
            } else {
                self.shift();
                other.shift();
            }
            if self.denominator == 0 && other.denominator == 0 {
                *self = URational::nan();
                return;
            } else if self.denominator == 0 {
                return;
            } else if other.denominator == 0 {
                *self = *other;
                return;
            }
            if self.denominator == other.denominator {
                self.numerator = if sub {
                    try_or!(continue self.numerator.checked_sub(other.numerator))
                } else {
                    try_or!(continue self.numerator.checked_add(other.numerator))
                };
                self.simplify();
                return;
            }
            let common = gcd(self.denominator, other.denominator);
            let c = try_or!(continue self.denominator.checked_mul(other.denominator/common));
            let a = c / self.denominator;
            let b = c / other.denominator;
            let n0 = try_or!(continue self.numerator.checked_mul(a));
            let n1 = try_or!(continue other.numerator.checked_mul(b));
            self.numerator = if sub {
                try_or!(continue n0.checked_sub(n1))
            } else {
                try_or!(continue n0.checked_add(n1))
            };
            self.denominator = c;
            self.simplify();
            return;
        }
    }

    fn mul_div(&mut self, other: &mut URational, div: bool) {
        if div {
            *other = other.reciprocal();
        }
        let mut first = true;
        loop {
            if first {
                first = false;
            } else {
                self.shift();
                other.shift();
            }
            if self.is_nan() {
                return;
            } else if other.is_nan() || (self.is_infinity() && other.is_zero()) || (self.is_zero() && other.is_infinity()) {
                *self = URational::nan();
                return;
            } else if !self.is_signed() {
                return;
            } else if !other.is_signed() {
                *self = *other;
                return;
            }
            let ndc = gcd(self.numerator, other.denominator);
            self.numerator /= ndc;
            other.denominator /= ndc;
            let dnc = gcd(self.denominator, other.numerator);
            self.denominator /= dnc;
            other.numerator /= dnc;
            let n = try_or!(continue self.numerator.checked_mul(other.numerator));
            self.denominator = try_or!(continue self.denominator.checked_mul(other.denominator));
            self.numerator = n;
            return;
        }
    }

    fn rem_div(&mut self, other: &mut URational) {
        let mut first = true;
        loop {
            if first {
                first = false;
            } else {
                self.shift();
                other.shift();
            }
            if self.is_nan() {
                return;
            } else if other.is_nan() {
                *self = URational::nan();
                return;
            } else if other.is_zero() || self.is_infinity() {
                *self = URational::zero();
                return;
            } else if other.is_infinity() {
                return;
            }
            if self.denominator == other.denominator {
                self.numerator = try_or!(continue self.numerator.checked_rem(other.numerator));
                self.simplify();
                return;
            }
            let common = gcd(self.denominator, other.denominator);
            let c = try_or!(continue self.denominator.checked_mul(other.denominator/common));
            let a = c / self.denominator;
            let b = c / other.denominator;
            let n0 = try_or!(continue self.numerator.checked_mul(a));
            let n1 = try_or!(continue other.numerator.checked_mul(b));
            self.numerator = try_or!(continue n0.checked_rem(n1));
            self.denominator = c;
            self.simplify();
            return;
        }
    }
}

impl PartialEq for URational {
    fn eq(&self, other: &URational) -> bool {
        self.numerator == other.numerator && self.denominator == other.denominator && (self.numerator != 0 || self.denominator != 0) && (other.numerator != 0 || other.denominator != 0)
    }
}

impl PartialOrd for URational {
    fn partial_cmp(&self, other: &URational) -> Option<Ordering> {
        if self.eq(other) {
            Some(Ordering::Equal)
        } else if (self.numerator == 0 && self.denominator == 0) || (other.numerator == 0 && other.denominator == 0) {
            None
        } else {
            let mut a = *self;
            let mut b = *other;
            let mut first = true;
            loop {
                if first {
                    first = false;
                } else {
                    a.shift();
                    b.shift();
                }
                let nd = try_or!(continue a.numerator.checked_mul(b.denominator));
                let dn = try_or!(continue a.denominator.checked_mul(b.numerator));
                if nd > dn {
                    return Some(Ordering::Greater)
                } else {
                    return Some(Ordering::Less)
                }
            }
        }
    }
}

impl fmt::Display for URational {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.denominator == 1 {
            write!(f, "{}", self.numerator)
        } else if self.denominator == 0 {
            if self.numerator == 0 {
                write!(f, "NaN")
            } else {
                write!(f, "∞")
            }
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}

impl fmt::Debug for URational {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "({}/{})", self.numerator, self.denominator)
    }
}

/// A type representing a signed projectively-extended rational number
///
/// # Example
///
/// ```
/// use extended_rational::Rational;
///
/// let a = Rational::new(3, 17);
/// let b = Rational::new(-4, 7);
///
/// assert_eq!(a+b, Rational::new(-47, 119));
/// ```
#[derive(Copy, Clone)]
pub struct Rational {
    unsigned: URational,
    negative: bool,
}

impl Rational {
    /// Create a new signed rational with the given numerator and denominator
    pub fn new(numerator: i64, denominator: i64) -> Rational {
        let take_sign = |signed: i64| {
            (
                if signed == i64::MIN {
                    i64::MAX as u64 + 1
                } else {
                    signed.abs() as u64
                },
                signed < 0,
            )
        };
        let (n, sn) = take_sign(numerator);
        let (d, sd) = take_sign(denominator);
        Rational::new_raw(URational::new(n, d), sn != sd)
    }

    /// Create a new signed rational with the given unsigned rational and sign
    pub fn new_raw(unsigned: URational, negative: bool) -> Rational {
        Rational {
            unsigned,
            negative: if unsigned.is_signed() {
                negative
            } else {
                false
            },
        }
    }

    /// Returns the underlying unsigned rational of this rational
    #[inline(always)] pub fn unsigned(&self) -> URational { self.unsigned }

    /// Returns the underlying sign of this rational
    #[inline(always)] pub fn sign(&self) -> bool { self.negative }

    /// Returns the reciprocal of this rational
    #[inline] pub fn reciprocal(&self) -> Rational { Rational { unsigned: self.unsigned.reciprocal(), negative: self.negative } }

    /// Returns the negative reciprocal of this rational
    #[inline] pub fn negative_reciprocal(&self) -> Rational { Rational::new_raw( self.unsigned.reciprocal(), !self.negative) }

    /// Returns the complexity of this rational (max of absolute values of numerator and denominator)
    #[inline(always)] pub fn complexity(&self) -> u64 { self.unsigned.complexity() }

    /// Returns the smallest value a signed rational can store
    #[inline(always)] pub fn min_value() -> Rational { Rational { unsigned: URational { numerator: u64::MAX, denominator: 1 }, negative: true } }

    /// Returns the smallest positive value a signed rational can store
    #[inline(always)] pub fn min_pos_value() -> Rational { Rational { unsigned: URational { numerator: 1, denominator: u64::MAX }, negative: false } }

    /// Returns the largest negative value a signed rational can store
    #[inline(always)] pub fn max_neg_value() -> Rational { Rational { unsigned: URational { numerator: 1, denominator: u64::MAX }, negative: true } }

    /// Returns the largest value a signed rational can store
    #[inline(always)] pub fn max_value() -> Rational { Rational { unsigned: URational { numerator: u64::MAX, denominator: 1 }, negative: false } }

    /// Returns a signed rational representing `NaN`
    #[inline(always)] pub fn nan() -> Rational { Rational { unsigned: URational { numerator: 0, denominator: 0 }, negative: false } }

    /// Returns a signed rational representing `0`
    #[inline(always)] pub fn zero() -> Rational { Rational { unsigned: URational { numerator: 0, denominator: 1 }, negative: false } }

    /// Returns a signed rational representing `∞`
    #[inline(always)] pub fn infinity() -> Rational { Rational { unsigned: URational { numerator: 1, denominator: 0 }, negative: false } }

    /// Returns a signed rational representing `1`
    #[inline(always)] pub fn one() -> Rational { Rational { unsigned: URational { numerator: 1, denominator: 1 }, negative: false } }

    /// Returns a signed rational representing `-1`
    #[inline(always)] pub fn negative_one() -> Rational { Rational { unsigned: URational { numerator: 1, denominator: 1 }, negative: true } }

    /// Returns `true` if this rational is `NaN` and `false` otherwise
    #[inline(always)] pub fn is_nan(&self) -> bool { self.unsigned.is_nan() }

    /// Returns `true` if this rational is `0` and `false` otherwise
    #[inline(always)] pub fn is_zero(&self) -> bool { self.unsigned.is_zero() }

    /// Returns `true` if this rational is `∞` and `false` otherwise
    #[inline(always)] pub fn is_infinity(&self) -> bool { self.unsigned.is_infinity() }

    /// Returns `true` if this rational is a signed number (not `NaN`, `0`, or `∞`) and `false` otherwise
    #[inline(always)] pub fn is_signed(&self) -> bool { self.unsigned.is_signed() }

    /// Returns `true` if this rational is a negative number and `false` otherwise
    #[inline(always)] pub fn is_negative(&self) -> bool { self.negative }

    /// Returns `true` if this rational is a positive number and `false` otherwise
    #[inline] pub fn is_positive(&self) -> bool { self.unsigned.is_signed() && !self.negative }

    /// Returns this rational with no fractional component by rounding towards zero
    #[inline]
    pub fn floor(&self) -> Rational {
        Rational {
            unsigned: self.unsigned.floor(),
            negative: self.negative,
        }
    }

    /// Returns this rational with no fractional component by rounding
    #[inline]
    pub fn round(&self) -> Rational {
        Rational {
            unsigned: self.unsigned.round(),
            negative: self.negative,
        }
    }

    /// Returns this rational with no fractional component by rounding away from zero
    #[inline]
    pub fn ceil(&self) -> Rational {
        Rational {
            unsigned: self.unsigned.ceil(),
            negative: self.negative,
        }
    }

    /// Returns this rational without a negative sign
    #[inline]
    pub fn abs(&self) -> Rational {
        Rational {
            unsigned: self.unsigned,
            negative: false,
        }
    }

    fn check_sign(&mut self) {
        if !self.unsigned.is_signed() {
            self.negative = false;
        }
    }

    fn add_sub(&mut self, other: &mut Rational, sub: bool) {
        let negative = other.negative != sub;
        if self.negative != negative {
            if self.unsigned >= other.unsigned {
                self.unsigned.add_sub(&mut other.unsigned, true);
            } else {
                self.negative = negative;
                other.unsigned.add_sub(&mut self.unsigned, true);
                self.unsigned = other.unsigned;
            };
        } else {
            self.unsigned.add_sub(&mut other.unsigned, false);
        }
        self.check_sign();
    }

    fn mul_div(&mut self, other: &mut Rational, div: bool) {
        self.negative = self.negative != other.negative;
        self.unsigned.mul_div(&mut other.unsigned, div);
        self.check_sign();
    }

    fn rem_div(&mut self, other: &mut Rational) {
        self.unsigned.rem_div(&mut other.unsigned);
        self.check_sign();
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Rational) -> bool {
        self.unsigned == other.unsigned && (self.negative == other.negative || !(self.is_signed() || other.is_signed()))
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        if self.eq(other) {
            Some(Ordering::Equal)
        } else if self.is_infinity() || other.is_infinity() {
            None
        } else if let Some(ordering) = self.unsigned.partial_cmp(&other.unsigned) {
            if self.negative != other.negative {
                if self.negative {
                    Some(Ordering::Less)
                } else {
                    Some(Ordering::Greater)
                }
            } else if self.negative {
                if ordering == Ordering::Greater {
                    Some(Ordering::Less)
                } else {
                    Some(Ordering::Greater)
                }
            } else {
                Some(ordering)
            }
        } else {
            None
        }
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.negative {
            write!(f, "-{}", self.unsigned)
        } else {
            write!(f, "{}", self.unsigned)
        }
    }
}

impl fmt::Debug for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.negative {
            write!(f, "-{:?}", self.unsigned)
        } else {
            write!(f, "{:?}", self.unsigned)
        }
    }
}

impl_ops!(URational; AddAssign Add, add_assign add, add_sub false);
impl_ops!(URational; SubAssign Sub, sub_assign sub, add_sub true);
impl_ops!(URational; MulAssign Mul, mul_assign mul, mul_div false);
impl_ops!(URational; DivAssign Div, div_assign div, mul_div true);
impl_ops!(URational; RemAssign Rem, rem_assign rem, rem_div);

impl_ops!(Rational; AddAssign Add, add_assign add, add_sub false);
impl_ops!(Rational; SubAssign Sub, sub_assign sub, add_sub true);
impl_ops!(Rational; MulAssign Mul, mul_assign mul, mul_div false);
impl_ops!(Rational; DivAssign Div, div_assign div, mul_div true);
impl_ops!(Rational; RemAssign Rem, rem_assign rem, rem_div);

impl Neg for Rational {
    type Output = Rational;

    fn neg(self) -> Rational {
        Rational {
            unsigned: self.unsigned,
            negative: !self.negative,
        }
    }
}

impl From<URational> for Rational {
    fn from(r: URational) -> Rational {
        Rational::new_raw(r, false)
    }
}

impl_u_from!(u64 u32 u16 u8);

impl_from!(i64 i32 i16 i8);
impl_to!(f64 f32);
