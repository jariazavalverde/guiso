use std::ops;

/// Used for numeric types with additive identity.
///
/// # Examples
///
/// ```
/// use guiso::identity::AddIdentity;
///
/// let zero: u32 = u32::zero();
///
/// assert_eq!(3, 3 + zero);
/// assert_eq!(2, zero + 2);
/// ```
pub trait AddIdentity<T = Self> {
    fn zero() -> T;
}

macro_rules! add_identity_impl {
    ($($t:ty)*) => ($(
        impl AddIdentity<$t> for $t {
            #[inline(always)]
            fn zero() -> $t {
                0 as $t
            }
        }
    )*)
}

add_identity_impl! {
    usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64
}

/// Used for numeric types with multiplicative identity.
///
/// # Examples
///
/// ```
/// use guiso::identity::MulIdentity;
///
/// let one: u32 = u32::one();
///
/// assert_eq!(3, 3 * one);
/// assert_eq!(2, one * 2);
/// ```
pub trait MulIdentity<T = Self> {
    fn one() -> T;
}

macro_rules! mul_identity_impl {
    ($($t:ty)*) => ($(
        impl MulIdentity<$t> for $t {
            #[inline(always)]
            fn one() -> $t {
                1 as $t
            }
        }
    )*)
}

mul_identity_impl! {
    usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64
}

#[inline(always)]
pub fn is_lt_zero<T>(n: &T) -> bool
where
    T: AddIdentity<T>,
    T: PartialOrd<T>,
{
    n < &T::zero()
}

#[inline(always)]
pub fn is_le_zero<T>(n: &T) -> bool
where
    T: AddIdentity<T>,
    T: PartialOrd<T>,
{
    n <= &T::zero()
}

#[inline(always)]
pub fn is_gt_zero<T>(n: &T) -> bool
where
    T: AddIdentity<T>,
    T: PartialOrd<T>,
{
    n > &T::zero()
}

#[inline(always)]
pub fn is_ge_zero<T>(n: &T) -> bool
where
    T: AddIdentity<T>,
    T: PartialOrd<T>,
{
    n >= &T::zero()
}

#[inline(always)]
pub fn is_eq_zero<T>(n: &T) -> bool
where
    T: AddIdentity<T>,
    T: PartialEq<T>,
{
    n == &T::zero()
}

#[inline(always)]
pub fn is_ne_zero<T>(n: &T) -> bool
where
    T: AddIdentity<T>,
    T: PartialEq<T>,
{
    n != &T::zero()
}

#[inline(always)]
pub fn succ<T>(n: T) -> T
where
    T: MulIdentity<T>,
    T: ops::Add<T, Output = T>,
{
    n + T::one()
}

#[inline(always)]
pub fn pred<T>(n: T) -> T
where
    T: MulIdentity<T>,
    T: ops::Sub<T, Output = T>,
{
    n - T::one()
}
