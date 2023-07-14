/// Assert that this code is unreachable.
///
/// With debug assertions, expands to [`unreachable`], otherwise
/// [`core::hint::unreachable_unchecked`].
#[macro_export]
macro_rules! debug_unreachable {
    ($($tt:tt)*) =>{
        if ::core::cfg!(debug_assertions) {
            ::core::unreachable!($($tt)*)
        } else {
            unsafe { ::core::hint::unreachable_unchecked() }
        }
    };
}

/// Assert that the given condition is false.
///
/// With debug assertions, this expands to a panic, otherwise
/// [`core::hint::unreachable_unchecked`].
#[macro_export]
macro_rules! debug_impossible {
    ($cond:expr $(, $( $tt:tt )* )? ) => {
        if $cond {
        if ::core::cfg!(debug_assertions) {
            ::core::panic!($( $( $tt )* )?)
        } else {
            unsafe { ::core::hint::unreachable_unchecked() }
        }
        }
    };
}

/// A type which can have behavior similar to [`debug_unreachable`]
pub trait UnreachableExpect {
    /// The type which we expect to produce
    type Target;

    /// Produce the [`Self::Target`] value, or assert unreachable.
    ///
    /// Like with [`debug_unreachable`], this will panic with debug assertions, but will be UB when
    /// optimized for release mode.
    fn expect_unreachable(self, msg: &str) -> Self::Target;
}

impl<T> UnreachableExpect for Option<T> {
    type Target = T;

    #[inline(always)]
    #[cfg_attr(debug_assertions, track_caller)]
    fn expect_unreachable(self, msg: &str) -> Self::Target {
        if ::core::cfg!(debug_assertions) {
            self.expect(msg)
        } else {
            self.unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() })
        }
    }
}

impl<T, E: core::fmt::Debug> UnreachableExpect for Result<T, E> {
    type Target = T;

    #[inline(always)]
    #[cfg_attr(debug_assertions, track_caller)]
    fn expect_unreachable(self, msg: &str) -> Self::Target {
        if ::core::cfg!(debug_assertions) {
            self.expect(msg)
        } else {
            self.unwrap_or_else(|_| unsafe { core::hint::unreachable_unchecked() })
        }
    }
}
