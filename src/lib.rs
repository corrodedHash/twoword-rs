use num_traits::{
    ops::overflowing::OverflowingAdd, Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, Num,
    NumCast, One, PrimInt, Saturating, Zero,
};
use std::{convert::TryFrom, fmt::Debug};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct TwoWord<T> {
    pub higher: T,
    pub lower: T,
}

impl<T> TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    #[inline]
    pub fn mult(a: T, b: T) -> Self {
        let halfsize_bits = T::max_value().count_ones() as usize / 2;
        let halfsize_mask = T::max_value() >> halfsize_bits;
        let hi = |n: T| n >> halfsize_bits;
        let lo = |n: T| halfsize_mask & n;
        // a = (a_hi * 2**halfsize_bits + a_lo)
        // b = (b_hi * 2**halfsize_bits + b_lo)
        // r = a_lo * b_lo + (a_hi * b_lo + a_lo * b_hi) * 2**(halfsize_bits) + a_hi * b_hi * 2**(halfsize_bits*2)
        // r = s3 * 2**(halfsize_bits * 3) + s2 * 2**(halfsize_bits*2) + s1 * 2**(halfsize_bits) + s0
        // |ah| |al|   |bh| |bl|
        // 1001 1010 * 1111 0101
        // =====================
        //             0011 0010    al * bl
        //        1001 0110         al * bh
        //        0010 1101         ah * bl
        //   1000 0111              ah * bh
        //    s3   s2   s1   s0
        let s0;
        let mut s1;
        let mut s2;
        let s3;
        let mut x = lo(a) * lo(b);
        s0 = lo(x);
        x = hi(a) * lo(b) + hi(x);
        s1 = lo(x);
        s2 = hi(x);
        x = s1 + lo(a) * hi(b);
        s1 = lo(x);
        x = s2 + hi(a) * hi(b) + hi(x);
        s2 = lo(x);
        s3 = hi(x);
        let result = s1 << halfsize_bits | s0;
        let carry = s3 << halfsize_bits | s2;
        Self {
            higher: carry,
            lower: result,
        }
    }
    fn lower_bitcount() -> u32 {
        T::max_value().count_ones()
    }
    pub fn divmod(mut self, rhs: Self) -> (Self, Self) {
        let mut result = Self {
            higher: T::zero(),
            lower: T::zero(),
        };
        let one = Self {
            higher: T::zero(),
            lower: T::one(),
        };
        assert!(
            rhs.higher != T::zero() || rhs.lower != T::zero(),
            "Division by zero"
        );
        let divisor_log = rhs.leading_zeros();
        while self >= rhs {
            let dividend_log = self.leading_zeros();
            let divisor_log_diff = (divisor_log - dividend_log) as usize;
            if rhs << divisor_log_diff <= self {
                self -= rhs << divisor_log_diff;
                result += one << divisor_log_diff
            } else {
                self -= rhs << (divisor_log_diff - 1);
                result += one << (divisor_log_diff - 1)
            }
        }
        (result, self)
    }
}

impl<T> std::ops::Shl<usize> for TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    type Output = Self;
    fn shl(self, rhs: usize) -> <Self as std::ops::Shl<usize>>::Output {
        let lower_bitcount = Self::lower_bitcount() as usize;
        if rhs == 0 {
            return self;
        }
        if rhs >= lower_bitcount {
            return Self {
                higher: self.lower << (rhs - lower_bitcount),
                lower: T::zero(),
            };
        }
        Self {
            lower: self.lower << rhs,
            higher: (self.higher << rhs) | (self.lower >> (lower_bitcount - rhs)),
        }
    }
}
impl<T> std::ops::Shr<usize> for TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    type Output = Self;
    fn shr(self, rhs: usize) -> <Self as std::ops::Shr<usize>>::Output {
        let lower_bitcount = Self::lower_bitcount() as usize;
        if rhs == 0 {
            return self;
        }
        if rhs >= lower_bitcount {
            return Self {
                lower: self.higher >> (rhs - lower_bitcount),
                higher: T::zero(),
            };
        }
        Self {
            higher: self.higher >> rhs,
            lower: (self.lower >> rhs) | (self.higher << (lower_bitcount - rhs)),
        }
    }
}

impl<T> std::ops::Shl<u32> for TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    type Output = Self;
    fn shl(self, rhs: u32) -> Self::Output {
        <Self as std::ops::Shl<usize>>::shl(self, rhs as usize)
    }
}

impl<T> std::ops::Shr<u32> for TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    type Output = Self;
    fn shr(self, rhs: u32) -> Self::Output {
        <Self as std::ops::Shr<usize>>::shr(self, rhs as usize)
    }
}
impl<T> std::ops::ShlAssign<u32> for TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    fn shl_assign(&mut self, rhs: u32) {
        *self = <Self as std::ops::Shl<u32>>::shl(*self, rhs);
    }
}

impl<T> std::ops::ShrAssign<u32> for TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    fn shr_assign(&mut self, rhs: u32) {
        *self = <Self as std::ops::Shr<u32>>::shr(*self, rhs);
    }
}

impl<T> std::ops::Add for TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    type Output = Self;
    fn add(self, rhs: Self) -> <Self as std::ops::Add<Self>>::Output {
        let (lower, carry) = self.lower.overflowing_add(&rhs.lower);

        Self {
            lower,
            higher: self.higher + rhs.higher + if carry { T::one() } else { T::zero() },
        }
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::Add<&'_ Self> for TwoWord<T> {
    type Output = Self;

    fn add(self, rhs: &'_ Self) -> Self::Output {
        self + *rhs
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::AddAssign for TwoWord<T> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::AddAssign<&'_ Self> for TwoWord<T> {
    fn add_assign(&mut self, rhs: &'_ Self) {
        *self = *self + rhs;
    }
}

impl<T> std::ops::Sub for TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    type Output = Self;
    fn sub(self, rhs: Self) -> <Self as std::ops::Sub<Self>>::Output {
        if let Some(lower) = self.lower.checked_sub(&rhs.lower) {
            return Self {
                lower,
                higher: self.higher - rhs.higher,
            };
        }
        let msb_mask = T::one() << (Self::lower_bitcount() - 1) as usize;
        let msb_filter = !msb_mask;
        let result = (self.lower | msb_mask) - (rhs.lower & msb_filter);

        let result_msb_one =
            ((self.lower & msb_mask) == T::zero()) ^ ((rhs.lower & msb_mask) != T::zero());

        // Don't understand it, but we need to set the bit to 1 when we changed exactly one of the two msb's
        let lower = if result_msb_one {
            result | msb_mask
        } else {
            result
        };

        Self {
            lower,
            higher: self.higher - rhs.higher - T::one(),
        }
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::Sub<&'_ Self> for TwoWord<T> {
    type Output = Self;
    fn sub(self, rhs: &'_ Self) -> <Self as std::ops::Sub<Self>>::Output {
        self - *rhs
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::SubAssign for TwoWord<T> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::SubAssign<&'_ Self> for TwoWord<T> {
    fn sub_assign(&mut self, rhs: &'_ Self) {
        *self = *self - rhs;
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::Mul for TwoWord<T> {
    type Output = Self;

    #[inline]
    /// Not fully implemented yet, both high-parts need to be zero
    fn mul(self, rhs: Self) -> Self::Output {
        assert!(
            self.higher == T::zero() && rhs.higher == T::zero(),
            "(Possible) multiplication overflow"
        );
        Self::mult(self.lower, rhs.lower)
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::Mul<&'_ Self> for TwoWord<T> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: &'_ Self) -> Self::Output {
        self * *rhs
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::MulAssign for TwoWord<T> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}
impl<T: PrimInt + OverflowingAdd> std::ops::MulAssign<&'_ Self> for TwoWord<T> {
    #[inline]
    fn mul_assign(&mut self, rhs: &'_ Self) {
        *self = *self * rhs;
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::Div for TwoWord<T> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.divmod(rhs).0
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::Div<&'_ Self> for TwoWord<T> {
    type Output = Self;

    fn div(self, rhs: &'_ Self) -> Self::Output {
        self.divmod(*rhs).0
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::DivAssign for TwoWord<T> {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}
impl<T: PrimInt + OverflowingAdd> std::ops::DivAssign<&'_ Self> for TwoWord<T> {
    fn div_assign(&mut self, rhs: &'_ Self) {
        *self = *self / rhs;
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::Rem for TwoWord<T> {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        self.divmod(rhs).1
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::Rem<&'_ Self> for TwoWord<T> {
    type Output = Self;

    fn rem(self, rhs: &'_ Self) -> Self::Output {
        self.divmod(*rhs).1
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::RemAssign for TwoWord<T> {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}
impl<T: PrimInt + OverflowingAdd> std::ops::RemAssign<&'_ Self> for TwoWord<T> {
    fn rem_assign(&mut self, rhs: &'_ Self) {
        *self = *self % rhs;
    }
}

impl<T> std::ops::BitAnd for TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self {
            lower: self.lower & rhs.lower,
            higher: self.higher & rhs.higher,
        }
    }
}

impl<T> std::ops::BitOr for TwoWord<T>
where
    T: PrimInt + OverflowingAdd,
{
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self {
            lower: self.lower | rhs.lower,
            higher: self.higher | rhs.higher,
        }
    }
}

impl<T: PrimInt + OverflowingAdd> std::ops::BitXor for TwoWord<T> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self {
            lower: self.lower ^ rhs.lower,
            higher: self.higher ^ rhs.higher,
        }
    }
}
impl<T: PrimInt + OverflowingAdd> std::ops::Not for TwoWord<T> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self {
            lower: !self.lower,
            higher: !self.higher,
        }
    }
}

impl<T: PrimInt + Bounded + OverflowingAdd> Saturating for TwoWord<T> {
    fn saturating_add(self, v: Self) -> Self {
        if let Some(x) = self.checked_add(&v) {
            x
        } else {
            Self::max_value()
        }
    }

    fn saturating_sub(self, v: Self) -> Self {
        if let Some(x) = self.checked_sub(&v) {
            return x;
        }
        Self::min_value()
    }
}

impl<T: PrimInt + OverflowingAdd> num_traits::Bounded for TwoWord<T> {
    fn min_value() -> Self {
        Self {
            lower: T::zero(),
            higher: T::zero(),
        }
    }

    fn max_value() -> Self {
        Self {
            lower: T::max_value(),
            higher: T::max_value(),
        }
    }
}

impl<T: PrimInt + OverflowingAdd> num_traits::ops::overflowing::OverflowingAdd for TwoWord<T> {
    fn overflowing_add(&self, v: &Self) -> (Self, bool) {
        let (lower, carry) = self.lower.overflowing_add(&v.lower);
        let carry_bit = if carry { T::one() } else { T::zero() };
        let (higher, higher_carry) = self.higher.overflowing_add(&v.higher);
        let (higher, higher_carry_2) = higher.overflowing_add(&carry_bit);
        (Self { lower, higher }, higher_carry | higher_carry_2)
    }
}

impl<T: PrimInt + OverflowingAdd> CheckedAdd for TwoWord<T> {
    fn checked_add(&self, v: &Self) -> Option<Self> {
        let (lower, carry) = self.lower.overflowing_add(&v.lower);
        let carry_bit = if carry { T::one() } else { T::zero() };
        Some(Self {
            lower,
            higher: self
                .higher
                .checked_add(&v.higher)?
                .checked_add(&carry_bit)?,
        })
    }
}

impl<T: PrimInt + OverflowingAdd> CheckedSub for TwoWord<T> {
    fn checked_sub(&self, v: &Self) -> Option<Self> {
        if v > self {
            None
        } else {
            Some(*self - *v)
        }
    }
}

impl<T: PrimInt + OverflowingAdd> CheckedMul for TwoWord<T> {
    fn checked_mul(&self, v: &Self) -> Option<Self> {
        if self.higher > T::zero() || v.higher > T::zero() {
            return None;
        }
        Some(*self * *v)
    }
}

impl<T: PrimInt + OverflowingAdd> CheckedDiv for TwoWord<T> {
    fn checked_div(&self, v: &Self) -> Option<Self> {
        if v == &<Self as num_traits::Zero>::zero() {
            None
        } else {
            Some(self.divmod(*v).0)
        }
    }
}

impl<T: PrimInt + OverflowingAdd> num_traits::Zero for TwoWord<T> {
    fn zero() -> Self {
        Self {
            lower: T::zero(),
            higher: T::zero(),
        }
    }

    fn is_zero(&self) -> bool {
        self.lower.is_zero() && self.higher.is_zero()
    }
}

impl<T: PrimInt + OverflowingAdd> num_traits::One for TwoWord<T> {
    fn one() -> Self {
        Self {
            lower: T::one(),
            higher: T::zero(),
        }
    }
}

impl<T: PrimInt + OverflowingAdd> num_traits::WrappingAdd for TwoWord<T>
where
    T: num_traits::WrappingAdd,
{
    fn wrapping_add(&self, v: &Self) -> Self {
        let (lower, carry) = self.lower.overflowing_add(&v.lower);
        let carry_bit = if carry { T::one() } else { T::zero() };
        Self {
            lower,
            higher: self.higher.wrapping_add(&v.higher).wrapping_add(&carry_bit),
        }
    }
}

impl<T: PrimInt + OverflowingAdd> num_traits::WrappingSub for TwoWord<T>
where
    T: num_traits::WrappingSub,
{
    fn wrapping_sub(&self, v: &Self) -> Self {
        if self.lower >= v.lower {
            Self {
                lower: self.lower - v.lower,
                higher: self.lower.wrapping_sub(&v.higher),
            }
        } else {
            Self {
                lower: self.lower.wrapping_sub(&v.lower),
                higher: self.higher.wrapping_sub(&v.lower).wrapping_sub(&T::one()),
            }
        }
    }
}

impl<T: PrimInt + OverflowingAdd> num_traits::WrappingMul for TwoWord<T>
where
    T: num_traits::WrappingAdd,
{
    fn wrapping_mul(&self, v: &Self) -> Self {
        let mut result = Self::zero();
        if self.lower != T::zero() && v.lower != T::zero() {
            let ll = Self::mult(self.lower, v.lower);
            result += ll;
        }
        if self.higher != T::zero() && v.lower != T::zero() {
            let hl = Self::mult(self.higher, v.lower);
            result.higher.wrapping_add(&hl.lower);
        }
        if self.lower != T::zero() && v.higher != T::zero() {
            let lh = Self::mult(self.lower, v.higher);
            result.higher.wrapping_add(&lh.lower);
        }
        result
    }
}

impl<T: PrimInt + OverflowingAdd> num_traits::ToPrimitive for TwoWord<T> {
    fn to_i64(&self) -> Option<i64> {
        None
    }

    fn to_u64(&self) -> Option<u64> {
        if u64::MAX.count_ones() > Self::lower_bitcount() {
            Some(
                self.lower.to_u64().unwrap()
                    | self.higher.to_u64().unwrap() << Self::lower_bitcount() as usize,
            )
        } else if self.higher == T::zero() {
            self.lower.to_u64()
        } else {
            None
        }
    }
    fn to_u128(&self) -> Option<u128> {
        if u128::MAX.count_ones() > Self::lower_bitcount() {
            Some(
                self.lower.to_u128().unwrap()
                    | self.higher.to_u128().unwrap() << Self::lower_bitcount() as usize,
            )
        } else if self.higher == T::zero() {
            self.lower.to_u128()
        } else {
            None
        }
    }
}

impl<T: PrimInt + OverflowingAdd> NumCast for TwoWord<T> {
    fn from<O: num_traits::ToPrimitive>(n: O) -> Option<Self> {
        T::from(n).map(|x| Self {
            lower: x,
            higher: T::zero(),
        })
    }
}

impl<T: PrimInt + OverflowingAdd> Num for TwoWord<T> {
    type FromStrRadixErr = ();

    fn from_str_radix(_str: &str, _radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        todo!()
    }
}

impl<T: PrimInt + OverflowingAdd> PrimInt for TwoWord<T> {
    fn count_ones(self) -> u32 {
        self.lower.count_ones() + self.higher.count_ones()
    }

    fn count_zeros(self) -> u32 {
        self.lower.count_zeros() + self.higher.count_zeros()
    }

    fn leading_zeros(self) -> u32 {
        if self.higher.leading_zeros() == Self::lower_bitcount() {
            self.higher.leading_zeros() + self.lower.leading_zeros()
        } else {
            self.higher.leading_zeros()
        }
    }

    fn trailing_zeros(self) -> u32 {
        if self.lower.trailing_zeros() == Self::lower_bitcount() {
            self.higher.trailing_zeros() + self.lower.trailing_zeros()
        } else {
            self.lower.trailing_zeros()
        }
    }

    fn rotate_left(self, n: u32) -> Self {
        self.unsigned_shl(n) | self.unsigned_shr(2 * Self::lower_bitcount() - n)
    }

    fn rotate_right(self, n: u32) -> Self {
        self.unsigned_shr(n) | self.unsigned_shl(2 * Self::lower_bitcount() - n)
    }

    fn signed_shl(self, n: u32) -> Self {
        self.unsigned_shl(n)
    }

    fn signed_shr(self, n: u32) -> Self {
        if n == 0 {
            return self;
        }
        let msb_mask = Self::one() << (Self::max_value().count_ones() - 1) as usize;
        let negative = (self & msb_mask) != Self::zero();
        if negative {
            self.unsigned_shr(n) | !(Self::one() << (Self::max_value().count_ones() - n) as usize)
        } else {
            self.unsigned_shr(n)
        }
    }

    fn unsigned_shl(self, n: u32) -> Self {
        self << n as usize
    }

    fn unsigned_shr(self, n: u32) -> Self {
        self >> n as usize
    }

    fn swap_bytes(self) -> Self {
        Self {
            higher: self.lower.swap_bytes(),
            lower: self.higher.swap_bytes(),
        }
    }

    fn from_be(x: Self) -> Self {
        if x.lower == PrimInt::from_be(x.lower) {
            x
        } else {
            Self {
                lower: PrimInt::from_be(x.higher),
                higher: PrimInt::from_be(x.lower),
            }
        }
    }

    fn from_le(x: Self) -> Self {
        if x.lower == PrimInt::from_le(x.lower) {
            x
        } else {
            Self {
                lower: PrimInt::from_le(x.higher),
                higher: PrimInt::from_le(x.lower),
            }
        }
    }

    fn to_be(self) -> Self {
        if self.lower == self.lower.to_be() {
            self
        } else {
            Self {
                lower: self.higher.to_be(),
                higher: self.lower.to_be(),
            }
        }
    }

    fn to_le(self) -> Self {
        if self.lower == self.lower.to_le() {
            self
        } else {
            Self {
                lower: self.higher.to_le(),
                higher: self.lower.to_le(),
            }
        }
    }

    fn pow(mut self, mut exp: u32) -> Self {
        let mut result = if exp % 2 == 1 { self } else { Self::one() };
        exp /= 2;
        while exp > 0 {
            self = self * self;
            if exp % 2 == 1 {
                result *= self;
            }
            exp /= 2;
        }
        result
    }
}

impl TryFrom<TwoWord<u128>> for u128 {
    type Error = ();

    fn try_from(value: TwoWord<u128>) -> Result<Self, Self::Error> {
        if value.higher != 0u128 {
            Err(())
        } else {
            Ok(value.lower)
        }
    }
}

impl From<u128> for TwoWord<u128> {
    fn from(v: u128) -> Self {
        Self {
            lower: v,
            higher: 0,
        }
    }
}

#[cfg(test)]
mod tests {

    use super::TwoWord;
    fn to_two_word(n: u16) -> TwoWord<u8> {
        TwoWord {
            lower: (n & 0b11111111) as u8,
            higher: (n >> 8) as u8,
        }
    }

    #[test]
    fn test_two_word_mult() {
        for f1 in 0..=u8::MAX {
            for f2 in 0..=u8::MAX {
                assert_eq!(TwoWord::mult(f1, f2), to_two_word(f1 as u16 * f2 as u16));
            }
        }
    }
    #[test]
    fn test_two_word_arith() {
        for i in 0u16..10000 {
            let f1g = i.wrapping_mul(16329).wrapping_add(17819);
            let f2g = i.wrapping_mul(28263).wrapping_add(8942);
            assert_eq!(
                to_two_word(f1g & (u16::MAX >> 1)) + to_two_word(f2g & (u16::MAX >> 1)),
                to_two_word((f1g & (u16::MAX >> 1)) + (f2g & (u16::MAX >> 1)))
            );
            if f1g > f2g {
                assert_eq!(to_two_word(f1g) - to_two_word(f2g), to_two_word(f1g - f2g));
            } else {
                assert_eq!(to_two_word(f2g) - to_two_word(f1g), to_two_word(f2g - f1g));
            }
            if f2g != 0 {
                assert_eq!(
                    TwoWord::divmod(to_two_word(f1g), to_two_word(f2g)),
                    (to_two_word(f1g / f2g), to_two_word(f1g % f2g))
                );
            }
        }
    }

    #[test]
    fn test_two_word_cmp() {
        assert!(
            TwoWord {
                higher: 2u8,
                lower: 0
            } > TwoWord {
                lower: 4u8,
                higher: 0
            }
        );
    }

    #[test]
    fn test_two_word_shift() {
        for i in 0u16..10000 {
            let f1g = i.wrapping_mul(16329).wrapping_add(17819) & (u16::MAX >> 1);
            for s in 0usize..=15 {
                assert_eq!(to_two_word(f1g) >> s, to_two_word(f1g >> s));
                assert_eq!(to_two_word(f1g) << s, to_two_word(f1g << s));
            }
        }
    }
}
