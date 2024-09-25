macro_rules! num_identity {
    ($type:ident) => {
        impl AddIdentity<$type> for $type {
            #[inline(always)]
            fn zero() -> $type {
                0 as $type
            }
        }

        impl MulIdentity<$type> for $type {
            #[inline(always)]
            fn one() -> $type {
                1 as $type
            }
        }
    };
}

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
pub trait AddIdentity<T> {
    fn zero() -> T;
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
pub trait MulIdentity<T> {
    fn one() -> T;
}

num_identity!(u8);
num_identity!(u16);
num_identity!(u32);
num_identity!(u64);
num_identity!(u128);
num_identity!(i8);
num_identity!(i16);
num_identity!(i32);
num_identity!(i64);
num_identity!(i128);
num_identity!(f32);
num_identity!(f64);
