macro_rules! identity {
    ($type:ident, $zero:expr, $one:expr) => {
        impl AddIdentity<$type> for $type {
            fn zero() -> $type {
                $zero
            }
        }

        impl MulIdentity<$type> for $type {
            fn one() -> $type {
                $one
            }
        }
    };
}
pub trait AddIdentity<T> {
    fn zero() -> T;
}

pub trait MulIdentity<T> {
    fn one() -> T;
}

identity!(u8, 0, 1);
identity!(u16, 0, 1);
identity!(u32, 0, 1);
identity!(u64, 0, 1);
identity!(u128, 0, 1);
identity!(i8, 0, 1);
identity!(i16, 0, 1);
identity!(i32, 0, 1);
identity!(i64, 0, 1);
identity!(i128, 0, 1);
identity!(f32, 0.0, 1.0);
identity!(f64, 0.0, 1.0);
