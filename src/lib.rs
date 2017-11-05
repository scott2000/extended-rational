//! Provides implementations of high-accuracy projectively-extended rational numbers
//! and macros for creating them
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
//!
//! # Panics
//!
//! No operation should ever panic. Operations that overflow round each input to a
//! simpler fraction until they can succeed. Any invalid operations should
//! return `NaN` instead of panicking.
//!
//! # Additional Features
//!
//! For use with the [bit manager] crate, add this to your `Cargo.toml`:
//!
//! ```toml
//! [features]
//! default = ["extended-rational/bit_manager_enabled"]
//! ```
//!
//! [bit manager]: http://docs.rs/bit_manager

#![deny(missing_docs, trivial_casts, unused_macros)]

#[macro_use]
#[cfg(feature="bit_manager_enabled")]
extern crate bit_manager_derive;

use std::*;
use std::cmp::*;
use std::ops::*;

/// A macro for creating a new [signed rational](struct.Rational.html) using a given ratio or decimal
///
/// *Floating-point conversions may be wrong due to small rounding errors.*
///
/// # Alternatives
///
/// * `ratio!(n, d)` is equivalent to `Rational::from([n, d])`
/// * `ratio!(n)` is equivalent to `Rational::from(n)`
///
/// # Examples
///
/// ```
/// # #[macro_use]
/// # extern crate extended_rational;
/// # use extended_rational::Rational;
/// # fn main() {
/// let five_thirds = ratio!(5, 3);
/// let neg_seven_and_a_half = ratio!(-7.5);
///
/// assert_eq!(five_thirds, Rational::from([5, 3]));
/// assert_eq!(neg_seven_and_a_half, Rational::new(-15, 2));
/// # }
/// ```
#[macro_export]
macro_rules! ratio {
    ( $ n : expr , $ d : expr ) => ( $crate::Rational::from([$n, $d]) );
    ( $ n : expr ) => ( $crate::Rational::from($n) );
}

/// A macro for creating a new [unsigned rational](struct.URational.html) using a given ratio or decimal
///
/// *Floating-point conversions may be wrong due to small rounding errors.*
///
/// # Panics
///
/// On attempt to create negative rational. *Doesn't panic in optimized builds.*
///
/// # Alternatives
///
/// * `uratio!(n, d)` is equivalent to `ratio!(n, d).try_unsigned()`
/// * `uratio!(n)` is equivalent to `ratio!(n).try_unsigned()`
///
/// # Examples
///
/// ```
/// # #[macro_use]
/// # extern crate extended_rational;
/// # use extended_rational::URational;
/// # fn main() {
/// let five_thirds = uratio!(5, 3);
/// let seventeen = uratio!(17);
///
/// assert_eq!(five_thirds, URational::new(5, 3));
/// assert_eq!(seventeen, URational::new(17, 1));
/// # }
/// ```
#[macro_export]
macro_rules! uratio {
    ( $ n : expr , $ d : expr ) => {{
        $crate::Rational::from([$n, $d]).try_unsigned()
    }};
    ( $ n : expr ) => {{
        $crate::Rational::from($n).try_unsigned()
    }};
}

macro_rules! try_or {
    (continue $x: expr) => {
        match $x {
            Some(x) => x,
            None => continue,
        }
    };
    (return $r: expr; $x: expr) => {
        match $x {
            Some(x) => x,
            None => return $r,
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
                /// Create a new unsigned rational with the given value.
                fn from(n: $t) -> URational {
                    URational::new(n as u64, 1)
                }
            }
            impl From<($t, $t)> for URational {
                /// Create a new unsigned rational with the given numerator and denominator tuple.
                fn from(tuple: ($t, $t)) -> URational {
                    let (n, d) = tuple;
                    URational::new(n as u64, d as u64)
                }
            }
            impl From<[$t; 2]> for URational {
                /// Create a new unsigned rational with the given numerator and denominator array.
                fn from(array: [$t; 2]) -> URational {
                    URational::new(array[0] as u64, array[1] as u64)
                }
            }
            impl From<$t> for Rational {
                /// Create a new signed rational with the given value.
                fn from(n: $t) -> Rational {
                    Rational::from(URational::from(n))
                }
            }
            impl From<($t, $t)> for Rational {
                /// Create a new signed rational with the given numerator and denominator tuple.
                fn from(tuple: ($t, $t)) -> Rational {
                    Rational::from(URational::from(tuple))
                }
            }
            impl From<[$t; 2]> for Rational {
                /// Create a new signed rational with the given numerator and denominator array.
                fn from(array: [$t; 2]) -> Rational {
                    Rational::from(URational::from(array))
                }
            }
        )+
    }
}

macro_rules! impl_from {
    ($($t: ty)+) => {
        $(
            impl From<$t> for Rational {
                /// Creates a new signed rational with the given value.
                fn from(n: $t) -> Rational {
                    Rational::new(n as i64, 1)
                }
            }
            impl From<($t, $t)> for Rational {
                /// Creates a new signed rational with the given numerator and denominator tuple.
                fn from(tuple: ($t, $t)) -> Rational {
                    let (n, d) = tuple;
                    Rational::new(n as i64, d as i64)
                }
            }
            impl From<[$t; 2]> for Rational {
                /// Creates a new signed rational with the given numerator and denominator array.
                fn from(array: [$t; 2]) -> Rational {
                    Rational::new(array[0] as i64, array[1] as i64)
                }
            }
        )+
    }
}

macro_rules! impl_float {
    ($($t: ty [$total: expr, $sig: expr])+) => {
        $(
            impl From<URational> for $t {
                /// Creates an approximation of the given unsigned rational.
                fn from(r: URational) -> $t {
                    (r.numerator as $t) / (r.denominator as $t)
                }
            }
            impl From<Rational> for $t {
                /// Creates an approximation of the given signed rational.
                fn from(r: Rational) -> $t {
                    (if r.negative { -1.0 } else { 1.0 }) * (r.unsigned.numerator as $t) / (r.unsigned.denominator as $t)
                }
            }
            impl From<$t> for Rational {
                /// Attempts to approximate the given floating-point number with a signed rational.
                ///
                /// ## Rounding
                ///
                /// * If the exponent is too large, `∞` will be returned
                /// * If the exponent is too small, `0` will be returned
                fn from(f: $t) -> Rational {
                    match f.classify() {
                        std::num::FpCategory::Infinite => return Rational::infinity(),
                        std::num::FpCategory::Nan => return Rational::nan(),
                        std::num::FpCategory::Zero | std::num::FpCategory::Subnormal => return Rational::zero(),
                        _ => (),
                    }

                    let bits = f.to_bits() as u64;
                    let neg = (bits >> ($total - 1)) == 1;
                    let exponent = ((bits >> $sig) & ((1u64 << ($total - 1 - $sig)) - 1)) as i32 - ((1i32 << ($total - 2 - $sig)) - 1) - $sig;
                    let significand = (1u64 << $sig) + (bits & ((1u64 << $sig) - 1));

                    if exponent < 0 {
                        if let Some(modifier) = 1u64.checked_shl(-exponent as u32) {
                            Rational::new_raw(URational::new(significand, modifier), neg)
                        } else {
                            Rational::zero()
                        }
                    } else {
                        if let Some(sig_mod) = significand.checked_shl(exponent as u32) {
                            Rational::new_raw(URational::new(sig_mod, 1), neg)
                        } else {
                            Rational::infinity()
                        }
                    }
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
    };
    ($assign: ident $non: ident, $assign_name: ident $non_name: ident, $f: ident $($b: expr)*) => {
        impl_ops!(URational; $assign $non, $assign_name $non_name, $f $($b)*);
        impl_ops!(Rational; $assign $non, $assign_name $non_name, $f $($b)*);
    }
}

/// Returns the greatest common divisor of two numbers.
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let c = b;
        b = a % b;
        a = c;
    }
    a
}

/// Returns the least common multiple of two numbers
/// or `None` if the calculation overflows.
pub fn lcm(a: u64, b: u64) -> Option<u64> {
    a.checked_mul(b/gcd(a, b))
}

/// A type representing an unsigned projectively-extended rational number
///
/// Subtracting a large number from a smaller one always returns `0` unless
/// the larger number is `∞`.
///
/// # Examples
///
/// ```
/// use extended_rational::URational;
///
/// let a = URational::new(3, 17);
/// let b = URational::new(4, 7);
///
/// assert_eq!(a+b, URational::new(89, 119));
/// ```
///
/// Use the [uratio!](macro.uratio.html) macro for more convenient use.
///
/// ```
/// # #[macro_use]
/// # extern crate extended_rational;
/// # #[allow(unused_variables)]
/// # fn main() {
/// let a = uratio!(3, 17);
/// let b = uratio!(4, 7);
/// # }
/// ```
///
/// Or for easy conversions from primitive types.
///
/// ```
/// # #[macro_use]
/// # extern crate extended_rational;
/// # #[allow(unused_variables)]
/// # fn main() {
/// let a = uratio!(343.863);
/// let b = uratio!(2u8);
/// # }
/// ```
#[derive(Copy, Clone)]
#[cfg_attr(feature="bit_manager_enabled", derive(BitStore))]
pub struct URational {
    numerator: u64,
    denominator: u64,
}

impl URational {
    /// Create a new unsigned rational with the given numerator and denominator.
    pub fn new(numerator: u64, denominator: u64) -> URational {
        let mut r = URational {
            numerator,
            denominator,
        };
        r.simplify();
        r
    }

    /// Returns the numerator of this rational.
    #[inline(always)] pub fn numerator(self) -> u64 { self.numerator }

    /// Returns the numerator of this rational mutably.
    #[inline(always)] pub fn numerator_mut(&mut self) -> &mut u64 { &mut self.numerator }

    /// Returns the denominator of this rational.
    #[inline(always)] pub fn denominator(self) -> u64 { self.denominator }

    /// Returns the denominator of this rational mutably.
    #[inline(always)] pub fn denominator_mut(&mut self) -> &mut u64 { &mut self.denominator }

    /// Returns the smallest value an unsigned rational can store.
    #[inline(always)] pub fn min_value() -> URational { URational { numerator: 0, denominator: 1 } }

    /// Returns the smallest non-zero value an unsigned rational can store.
    #[inline(always)] pub fn min_pos_value() -> URational { URational { numerator: 1, denominator: u64::MAX } }

    /// Returns the largest value an unsigned rational can store.
    #[inline(always)] pub fn max_value() -> URational { URational { numerator: u64::MAX, denominator: 1 } }

    /// Returns an unsigned rational representing `NaN`.
    #[inline(always)] pub fn nan() -> URational { URational { numerator: 0, denominator: 0 } }

    /// Returns an unsigned rational representing `0`.
    #[inline(always)] pub fn zero() -> URational { URational { numerator: 0, denominator: 1 } }

    /// Returns an unsigned rational representing `∞`.
    #[inline(always)] pub fn infinity() -> URational { URational { numerator: 1, denominator: 0 } }

    /// Returns an unsigned rational representing `1`.
    #[inline(always)] pub fn one() -> URational { URational { numerator: 1, denominator: 1 } }

    /// Returns `true` if this rational is `NaN` and `false` otherwise.
    #[inline] pub fn is_nan(self) -> bool { self.numerator == 0 && self.denominator == 0 }

    /// Returns `true` if this rational is `0` and `false` otherwise.
    #[inline] pub fn is_zero(self) -> bool { self.numerator == 0 && self.denominator != 0 }

    /// Returns `true` if this rational is `∞` and `false` otherwise.
    #[inline] pub fn is_infinity(self) -> bool { self.numerator != 0 && self.denominator == 0 }

    /// Returns `true` if this rational is a signed number (not `NaN`, `0`, or `∞`) and `false` otherwise.
    #[inline] pub fn is_signed(self) -> bool { self.numerator != 0 && self.denominator != 0 }

    /// Returns the reciprocal of this rational.
    #[inline] pub fn reciprocal(self) -> URational { URational { numerator: self.denominator, denominator: self.numerator } }

    /// Returns the complexity of this rational (max of numerator and denominator).
    #[inline] pub fn complexity(self) -> u64 { max(self.numerator, self.denominator) }

    /// Returns this rational with no fractional component by rounding down.
    pub fn floor(self) -> URational {
        if self.denominator != 0 {
            URational {
                numerator: self.numerator / self.denominator,
                denominator: 1,
            }
        } else {
            self
        }
    }

    /// Returns this rational with no fractional component by rounding.
    pub fn round(self) -> URational {
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
            self
        }
    }

    /// Returns this rational with no fractional component by rounding up.
    pub fn ceil(self) -> URational {
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
            self
        }
    }

    /// Computes `self + other`, returning `None` if rounding occurred.
    pub fn add_exact(mut self, mut other: URational) -> Option<URational> {
        if self.add_sub_exact(&mut other, false) {
            Some(self)
        } else {
            None
        }
    }

    /// Computes `self - other`, returning `None` if rounding occurred.
    pub fn sub_exact(mut self, mut other: URational) -> Option<URational> {
        if self.add_sub_exact(&mut other, true) {
            Some(self)
        } else {
            None
        }
    }

    /// Computes `self * other`, returning `None` if rounding occurred.
    pub fn mul_exact(mut self, mut other: URational) -> Option<URational> {
        if self.mul_div_exact(&mut other, false) {
            Some(self)
        } else {
            None
        }
    }

    /// Computes `self / other`, returning `None` if rounding occurred.
    pub fn div_exact(mut self, mut other: URational) -> Option<URational> {
        if self.mul_div_exact(&mut other, true) {
            Some(self)
        } else {
            None
        }
    }

    /// Computes `self % other`, returning `None` if rounding occurred.
    pub fn rem_exact(mut self, mut other: URational) -> Option<URational> {
        if self.rem_div_exact(&mut other) {
            Some(self)
        } else {
            None
        }
    }

    fn simplify(&mut self) {
        let common = gcd(self.numerator, self.denominator);
        if common > 1 {
            self.numerator /= common;
            self.denominator /= common;
        }
    }

    fn shift_partial(a: &mut u64) {
        if *a & 0b11 == 0b11 {
            *a >>= 1;
            *a += 1;
        } else {
            *a >>= 1;
        }
    }

    fn shift(&mut self) {
        URational::shift_partial(&mut self.numerator);
        URational::shift_partial(&mut self.denominator);
        self.simplify();
    }

    fn add_sub_exact(&mut self, other: &mut URational, sub: bool) -> bool {
        if sub && other > self && !other.is_infinity() {
            *self = URational::zero();
            return true;
        } else if self.denominator == 0 && other.denominator == 0 {
            *self = URational::nan();
            return true;
        } else if self.denominator == 0 {
            return true;
        } else if other.denominator == 0 {
            *self = *other;
            return true;
        } else if self.denominator == other.denominator {
            self.numerator = if sub {
                try_or!(return false; self.numerator.checked_sub(other.numerator))
            } else {
                try_or!(return false; self.numerator.checked_add(other.numerator))
            };
            self.simplify();
            return true;
        }
        let common = try_or!(return false; lcm(self.denominator, other.denominator));
        let self_mul = common / self.denominator;
        let other_mul = common / other.denominator;
        let n0 = try_or!(return false; self.numerator.checked_mul(self_mul));
        let n1 = try_or!(return false; other.numerator.checked_mul(other_mul));
        self.numerator = if sub {
            try_or!(return false; n0.checked_sub(n1))
        } else {
            try_or!(return false; n0.checked_add(n1))
        };
        self.denominator = common;
        self.simplify();
        true
    }

    fn mul_div_exact(&mut self, other: &mut URational, div: bool) -> bool {
        if div {
            *other = other.reciprocal();
        }
        if self.is_nan() {
            return true;
        } else if other.is_nan() || (self.is_infinity() && other.is_zero()) || (self.is_zero() && other.is_infinity()) {
            *self = URational::nan();
            return true;
        } else if !self.is_signed() {
            return true;
        } else if !other.is_signed() {
            *self = *other;
            return true;
        }
        let ndc = gcd(self.numerator, other.denominator);
        self.numerator /= ndc;
        other.denominator /= ndc;
        let dnc = gcd(self.denominator, other.numerator);
        self.denominator /= dnc;
        other.numerator /= dnc;
        let n = try_or!(return false; self.numerator.checked_mul(other.numerator));
        self.denominator = try_or!(return false; self.denominator.checked_mul(other.denominator));
        self.numerator = n;
        true
    }

    fn rem_div_exact(&mut self, other: &mut URational) -> bool {
        if self.is_nan() {
            return true;
        } else if other.is_nan() {
            *self = URational::nan();
            return true;
        } else if other.is_zero() || self.is_infinity() {
            *self = URational::zero();
            return true;
        } else if other.is_infinity() {
            return true;
        }
        if self.denominator == other.denominator {
            self.numerator = try_or!(return false; self.numerator.checked_rem(other.numerator));
            self.simplify();
            return true;
        }
        let common = try_or!(return false; lcm(self.denominator, other.denominator));
        let self_mul = common / self.denominator;
        let other_mul = common / other.denominator;
        let n0 = try_or!(return false; self.numerator.checked_mul(self_mul));
        let n1 = try_or!(return false; other.numerator.checked_mul(other_mul));
        self.numerator = try_or!(return false; n0.checked_rem(n1));
        self.denominator = common;
        self.simplify();
        true
    }

    fn add_sub(&mut self, other: &mut URational, sub: bool) {
        let mut first = true;
        loop {
            if first {
                first = false;
            } else if self >= other {
                self.shift();
            } else {
                other.shift();
            }
            if URational::add_sub_exact(self, other, sub) {
                return;
            }
        }
    }

    fn mul_div(&mut self, other: &mut URational, div: bool) {
        let mut first = true;
        loop {
            if first {
                first = false;
            } else if self >= other {
                self.shift();
            } else {
                other.shift();
            }
            if URational::mul_div_exact(self, other, div) {
                return;
            }
        }
    }

    fn rem_div(&mut self, other: &mut URational) {
        let mut first = true;
        loop {
            if first {
                first = false;
            } else if self >= other {
                self.shift();
            } else {
                other.shift();
            }
            if URational::rem_div_exact(self, other) {
                return;
            }
        }
    }
}

impl Default for URational {
    fn default() -> URational {
        URational::zero()
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
    /// Formats the rational.
    ///
    /// # Style
    ///
    /// * `NaN`, `∞`, and whole numbers are written directly
    /// * Ratios with complexities less than 100 are written as fractions (`n/d`)
    /// * All other numbers are written as decimals
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.denominator == 1 {
            write!(f, "{}", self.numerator)
        } else if self.denominator == 0 {
            if self.numerator == 0 {
                write!(f, "NaN")
            } else {
                write!(f, "∞")
            }
        } else if self.complexity() < 100 {
            write!(f, "{}/{}", self.numerator, self.denominator)
        } else {
            write!(f, "{}", self.numerator as f64 / self.denominator as f64)
        }
    }
}

impl fmt::Debug for URational {
    /// Formats the rational.
    ///
    /// # Style
    ///
    /// All numbers are written as fractions in parentheses `(n/d)`
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "({}/{})", self.numerator, self.denominator)
    }
}

/// A type representing a signed projectively-extended rational number
///
/// # Examples
///
/// ```
/// use extended_rational::Rational;
///
/// let a = Rational::new(3, 17);
/// let b = Rational::new(-4, 7);
///
/// assert_eq!(a+b, Rational::new(-47, 119));
/// ```
///
/// Use the [ratio!](macro.ratio.html) macro for more convenient use.
///
/// ```
/// # #[macro_use]
/// # extern crate extended_rational;
/// # #[allow(unused_variables)]
/// # fn main() {
/// let a = ratio!(3, 17);
/// let b = ratio!(-4, 7);
/// # }
/// ```
///
/// Or for easy conversions from primitive types.
///
/// ```
/// # #[macro_use]
/// # extern crate extended_rational;
/// # #[allow(unused_variables)]
/// # fn main() {
/// let a = ratio!(-77.332);
/// let b = ratio!(2u8);
/// # }
/// ```
#[derive(Copy, Clone)]
#[cfg_attr(feature="bit_manager_enabled", derive(BitStore))]
pub struct Rational {
    unsigned: URational,
    negative: bool,
}

impl Rational {
    /// Create a new signed rational with the given numerator and denominator.
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

    /// Create a new signed rational with the given unsigned rational and sign.
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

    /// Returns the underlying numerator of this rational.
    #[inline(always)] pub fn numerator(self) -> u64 { self.unsigned.numerator }

    /// Returns the underlying numerator of this rational mutably.
    #[inline(always)] pub fn numerator_mut(&mut self) -> &mut u64 { &mut self.unsigned.numerator }

    /// Returns the underlying denominator of this rational.
    #[inline(always)] pub fn denominator(self) -> u64 { self.unsigned.denominator }

    /// Returns the underlying denominator of this rational mutably.
    #[inline(always)] pub fn denominator_mut(&mut self) -> &mut u64 { &mut self.unsigned.denominator }

    /// Returns the underlying sign of this rational.
    #[inline(always)] pub fn sign(self) -> bool { self.negative }

    /// Returns the underlying sign of this rational mutably.
    #[inline(always)] pub fn sign_mut(&mut self) -> &mut bool { &mut self.negative }

    /// Returns the underlying unsigned rational of this rational.
    #[inline(always)] pub fn unsigned(self) -> URational { self.unsigned }

    /// Returns the underlying unsigned rational of this rational mutably.
    #[inline(always)] pub fn unsigned_mut(&mut self) -> &mut URational { &mut self.unsigned }

    /// Returns the underlying unsigned rational of this rational, panicking if sign is negative.
    ///
    /// *Does not panic in optimized builds.*
    #[inline]
    pub fn try_unsigned(self) -> URational {
        debug_assert!(!self.negative, "cannot create a URational with a negative sign.");
        self.unsigned
    }

    /// Returns the smallest value a signed rational can store.
    #[inline(always)] pub fn min_value() -> Rational { Rational { unsigned: URational { numerator: u64::MAX, denominator: 1 }, negative: true } }

    /// Returns the smallest positive value a signed rational can store.
    #[inline(always)] pub fn min_pos_value() -> Rational { Rational { unsigned: URational { numerator: 1, denominator: u64::MAX }, negative: false } }

    /// Returns the largest negative value a signed rational can store.
    #[inline(always)] pub fn max_neg_value() -> Rational { Rational { unsigned: URational { numerator: 1, denominator: u64::MAX }, negative: true } }

    /// Returns the largest value a signed rational can store.
    #[inline(always)] pub fn max_value() -> Rational { Rational { unsigned: URational { numerator: u64::MAX, denominator: 1 }, negative: false } }

    /// Returns a signed rational representing `NaN`.
    #[inline(always)] pub fn nan() -> Rational { Rational { unsigned: URational { numerator: 0, denominator: 0 }, negative: false } }

    /// Returns a signed rational representing `0`.
    #[inline(always)] pub fn zero() -> Rational { Rational { unsigned: URational { numerator: 0, denominator: 1 }, negative: false } }

    /// Returns a signed rational representing `∞`.
    #[inline(always)] pub fn infinity() -> Rational { Rational { unsigned: URational { numerator: 1, denominator: 0 }, negative: false } }

    /// Returns a signed rational representing `1`.
    #[inline(always)] pub fn one() -> Rational { Rational { unsigned: URational { numerator: 1, denominator: 1 }, negative: false } }

    /// Returns a signed rational representing `-1`.
    #[inline(always)] pub fn negative_one() -> Rational { Rational { unsigned: URational { numerator: 1, denominator: 1 }, negative: true } }

    /// Returns `true` if this rational is `NaN` and `false` otherwise.
    #[inline(always)] pub fn is_nan(self) -> bool { self.unsigned.is_nan() }

    /// Returns `true` if this rational is `0` and `false` otherwise.
    #[inline(always)] pub fn is_zero(self) -> bool { self.unsigned.is_zero() }

    /// Returns `true` if this rational is `∞` and `false` otherwise.
    #[inline(always)] pub fn is_infinity(self) -> bool { self.unsigned.is_infinity() }

    /// Returns `true` if this rational is a signed number (not `NaN`, `0`, or `∞`) and `false` otherwise.
    #[inline(always)] pub fn is_signed(self) -> bool { self.unsigned.is_signed() }

    /// Returns `true` if this rational is a negative number and `false` otherwise.
    #[inline(always)] pub fn is_negative(self) -> bool { self.negative }

    /// Returns the reciprocal of this rational.
    #[inline] pub fn reciprocal(self) -> Rational { Rational { unsigned: self.unsigned.reciprocal(), negative: self.negative } }

    /// Returns the negative reciprocal of this rational.
    #[inline] pub fn negative_reciprocal(self) -> Rational { Rational::new_raw( self.unsigned.reciprocal(), !self.negative) }

    /// Returns the complexity of this rational (max of absolute values of numerator and denominator).
    #[inline(always)] pub fn complexity(self) -> u64 { self.unsigned.complexity() }

    /// Returns `true` if this rational is a positive number and `false` otherwise.
    #[inline] pub fn is_positive(self) -> bool { self.unsigned.is_signed() && !self.negative }

    /// Returns this rational with no fractional component by rounding towards zero.
    #[inline]
    pub fn floor(self) -> Rational {
        Rational {
            unsigned: self.unsigned.floor(),
            negative: self.negative,
        }
    }

    /// Returns this rational with no fractional component by rounding.
    #[inline]
    pub fn round(self) -> Rational {
        Rational {
            unsigned: self.unsigned.round(),
            negative: self.negative,
        }
    }

    /// Returns this rational with no fractional component by rounding away from zero.
    #[inline]
    pub fn ceil(self) -> Rational {
        Rational {
            unsigned: self.unsigned.ceil(),
            negative: self.negative,
        }
    }

    /// Returns this rational without a negative sign.
    #[inline]
    pub fn abs(self) -> Rational {
        Rational {
            unsigned: self.unsigned,
            negative: false,
        }
    }

    /// Computes `self + other`, returning `None` if rounding occurred.
    pub fn add_exact(mut self, mut other: Rational) -> Option<Rational> {
        if self.add_sub_exact(&mut other, false) {
            Some(self)
        } else {
            None
        }
    }

    /// Computes `self - other`, returning `None` if rounding occurred.
    pub fn sub_exact(mut self, mut other: Rational) -> Option<Rational> {
        if self.add_sub_exact(&mut other, true) {
            Some(self)
        } else {
            None
        }
    }

    /// Computes `self * other`, returning `None` if rounding occurred.
    pub fn mul_exact(mut self, mut other: Rational) -> Option<Rational> {
        if self.mul_div_exact(&mut other, false) {
            Some(self)
        } else {
            None
        }
    }

    /// Computes `self / other`, returning `None` if rounding occurred.
    pub fn div_exact(mut self, mut other: Rational) -> Option<Rational> {
        if self.mul_div_exact(&mut other, true) {
            Some(self)
        } else {
            None
        }
    }

    /// Computes `self % other`, returning `None` if rounding occurred.
    pub fn rem_exact(mut self, mut other: Rational) -> Option<Rational> {
        if self.rem_div_exact(&mut other) {
            Some(self)
        } else {
            None
        }
    }

    fn check_sign(&mut self) {
        if !self.unsigned.is_signed() {
            self.negative = false;
        }
    }

    fn add_sub_exact(&mut self, other: &mut Rational, sub: bool) -> bool {
        let negative = other.negative != sub;
        if self.negative != negative {
            if self.unsigned >= other.unsigned {
                if !self.unsigned.add_sub_exact(&mut other.unsigned, true) {
                    return false;
                }
            } else {
                self.negative = negative;
                if !other.unsigned.add_sub_exact(&mut self.unsigned, true) {
                    return false;
                }
                self.unsigned = other.unsigned;
            };
        } else {
            if !self.unsigned.add_sub_exact(&mut other.unsigned, false) {
                return false;
            }
        }
        self.check_sign();
        true
    }

    fn mul_div_exact(&mut self, other: &mut Rational, div: bool) -> bool {
        self.negative = self.negative != other.negative;
        if self.unsigned.mul_div_exact(&mut other.unsigned, div) {
            self.check_sign();
            true
        } else {
            false
        }
    }

    fn rem_div_exact(&mut self, other: &mut Rational) -> bool {
        if self.unsigned.rem_div_exact(&mut other.unsigned) {
            self.check_sign();
            true
        } else {
            false
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

impl Default for Rational {
    fn default() -> Rational {
        Rational::zero()
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
    /// Formats the rational.
    ///
    /// # Style
    ///
    /// * `NaN`, `∞`, and whole numbers are written directly
    /// * Ratios with complexities less than 100 are written as fractions (`n/d`)
    /// * All other numbers are written as decimals
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.negative {
            write!(f, "-{}", self.unsigned)
        } else {
            write!(f, "{}", self.unsigned)
        }
    }
}

impl fmt::Debug for Rational {
    /// Formats the rational.
    ///
    /// # Style
    ///
    /// All numbers are written as fractions in parentheses `(n/d)`
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.negative {
            write!(f, "(-{}/{})", self.unsigned.numerator, self.unsigned.denominator)
        } else {
            write!(f, "({}/{})", self.unsigned.numerator, self.unsigned.denominator)
        }
    }
}

impl_ops!(AddAssign Add, add_assign add, add_sub false);
impl_ops!(SubAssign Sub, sub_assign sub, add_sub true);
impl_ops!(MulAssign Mul, mul_assign mul, mul_div false);
impl_ops!(DivAssign Div, div_assign div, mul_div true);
impl_ops!(RemAssign Rem, rem_assign rem, rem_div);

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
    /// Create a new signed rational from an unsigned rational.
    fn from(r: URational) -> Rational {
        Rational::new_raw(r, false)
    }
}

impl From<(URational, bool)> for Rational {
    /// Create a new signed rational from an unsigned rational and a sign.
    fn from(tuple: (URational, bool)) -> Rational {
        let (unsigned, negative) = tuple;
        Rational::new_raw(unsigned, negative)
    }
}

impl_float!(f64 [64, 52] f32 [32, 23]);

impl_u_from!(u64 u32 u16 u8);

impl_from!(i64 i32 i16 i8);