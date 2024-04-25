//! A collection of atomic "polyfill" routines, to use a term from JavaScript.
//!
//! ARMv6-M processors like the Cortex-M0 don't support the fancier atomic
//! operations available on most other ARM processors. In particular, they have
//! no atomic swap or read-modify-write instructions. This module provides
//! traits that use the native atomics on M3 and later, and fallback
//! implementations on M0.
//!
//! The M0 implementations rely on disabling interrupts. This means that:
//!
//! 1. They will hurt interrupt latency/jitter. However, the M0 already has
//!    pretty poor interrupt latency/jitter because of uninterruptible
//!    instructions and lack of BASEPRI. So, not a big loss.
//!
//! 2. They don't work in unprivileged mode. But, neither does most of `lilos`.
//!
//! This is exposed so that applications don't have to rewrite it for M0
//! support.

use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicU32, AtomicUsize, Ordering};

/// Basic atomic operations.
pub trait AtomicExt {
    /// Primitive type corresponding to this atomic type.
    type Value;

    /// Atomically exchange our current contents for `val`, returning the
    /// original contents.
    ///
    /// Replacement for `swap`.
    fn swap_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value;

    /// If `self`'s value is equal to `current`, atomically replace it with
    /// `new`, otherwise leave it untouched.
    ///
    /// Returns `Ok(current)` on success, `Err(actual_value)` on failure.
    ///
    /// Replacement for `compare_exchange`.
    fn compare_exchange_polyfill(&self, current: Self::Value, new: Self::Value, success: Ordering, failure: Ordering) -> Result<Self::Value, Self::Value>;

    /// Fetches the current value using `fetch_order`, applies `f` to it. If `f`
    /// produces `Some(new_value)`, attempts to swap the value that was read for
    /// `new_value`. If `f` produces `None`, stops.
    ///
    /// If the swap fails, the process repeats and `f` is called again with the
    /// new observed value.
    ///
    /// Replacement for `fetch_update`.
    fn fetch_update_polyfill(
        &self,
        set_order: Ordering,
        fetch_order: Ordering,
        f: impl FnMut(Self::Value) -> Option<Self::Value>
    ) -> Result<Self::Value, Self::Value>;
}

/// Atomic operations that apply to arithmetic types.
pub trait AtomicArithExt: AtomicExt {
    /// Atomically add `val` to our contents, returning the original value.
    fn fetch_add_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value;
    /// Atomically OR `val` into our contents, returning the original value.
    fn fetch_or_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value;
}

macro_rules! impl_atomic_polyfills {
    ($t:ty, $v:ty $(, $param:ident)?) => {
        // Native version
        #[cfg(feature = "has-native-rmw")]
        impl<$($param)?> AtomicExt for $t {
            type Value = $v;

            fn swap_polyfill(
                &self,
                val: Self::Value,
                ordering: Ordering,
            ) -> Self::Value {
                self.swap(val, ordering)
            }

            fn compare_exchange_polyfill(
                &self,
                current: Self::Value,
                new: Self::Value,
                success: Ordering,
                failure: Ordering,
            ) -> Result<Self::Value, Self::Value> {
                self.compare_exchange(current, new, success, failure)
            }

            fn fetch_update_polyfill(
                &self,
                set_order: Ordering,
                fetch_order: Ordering,
                f: impl FnMut(Self::Value) -> Option<Self::Value>,
            ) -> Result<Self::Value, Self::Value> {
                self.fetch_update(set_order, fetch_order, f)
            }
        }

        // Non-native version
        #[cfg(not(feature = "has-native-rmw"))]
        impl<$($param)?> AtomicExt for $t {
            type Value = $v;
        
            #[inline(always)]
            fn swap_polyfill(
                &self,
                val: Self::Value,
                ordering: Ordering,
            ) -> Self::Value {
                let (lo, so) = rmw_ordering(ordering);
                cortex_m::interrupt::free(|_| {
                    let x = self.load(lo);
                    self.store(val, so);
                    x
                })
            }

            fn compare_exchange_polyfill(
                &self,
                current: Self::Value,
                new: Self::Value,
                success: Ordering,
                failure: Ordering,
            ) -> Result<Self::Value, Self::Value> {
                let (lo, so) = rmw_ordering(success);
                cortex_m::interrupt::free(|_| {
                    let x = self.load(lo);
                    if x == current {
                        self.store(new, so);
                        Ok(x)
                    } else {
                        self.store(x, failure);
                        Err(x)
                    }
                })
            }

            fn fetch_update_polyfill(
                &self,
                set_order: Ordering,
                fetch_order: Ordering,
                mut f: impl FnMut(Self::Value) -> Option<Self::Value>
            ) -> Result<Self::Value, Self::Value> {
                let mut prev = self.load(fetch_order);
                while let Some(next) = f(prev) {
                    let cx_result = self.compare_exchange_polyfill(
                        prev,
                        next,
                        set_order,
                        fetch_order,
                    );
                    match cx_result {
                        Ok(x) => return Ok(x),
                        Err(change) => prev = change,
                    }
                }
                Err(prev)
            }
        }
    };
}

impl_atomic_polyfills!(AtomicU32, u32);
impl_atomic_polyfills!(AtomicUsize, usize);
impl_atomic_polyfills!(AtomicBool, bool);
impl_atomic_polyfills!(AtomicPtr<T>, *mut T, T);


macro_rules! impl_atomic_arith_polyfills {
    ($t:ty $(, $param:ident)?) => {
        // Native version
        #[cfg(feature = "has-native-rmw")]
        impl<$($param)?> AtomicArithExt for $t {
            fn fetch_add_polyfill(
                &self,
                val: Self::Value,
                ordering: Ordering,
            ) -> Self::Value {
                self.fetch_add(val, ordering)
            }

            fn fetch_or_polyfill(
                &self,
                val: Self::Value,
                ordering: Ordering,
            ) -> Self::Value {
                self.fetch_or(val, ordering)
            }
        }

        // Non-native version
        #[cfg(not(feature = "has-native-rmw"))]
        impl<$($param)?> AtomicArithExt for $t {
            fn fetch_add_polyfill(
                &self,
                val: Self::Value,
                ordering: Ordering,
            ) -> Self::Value {
                let (lo, so) = rmw_ordering(ordering);
                cortex_m::interrupt::free(|_| {
                    let x = self.load(lo);
                    self.store(x.wrapping_add(val), so);
                    x
                })
            }

            fn fetch_or_polyfill(
                &self,
                val: Self::Value,
                ordering: Ordering,
            ) -> Self::Value {
                let (lo, so) = rmw_ordering(ordering);
                cortex_m::interrupt::free(|_| {
                    let x = self.load(lo);
                    self.store(x | val, so);
                    x
                })
            }
        }
    };
}

impl_atomic_arith_polyfills!(AtomicUsize);
impl_atomic_arith_polyfills!(AtomicU32);

#[cfg(not(feature = "has-native-rmw"))]
#[inline(always)]
fn rmw_ordering(o: Ordering) -> (Ordering, Ordering) {
    match o {
        Ordering::AcqRel => (Ordering::Acquire, Ordering::Release),
        Ordering::Relaxed => (o, o),
        Ordering::SeqCst => (o, o),
        Ordering::Acquire => (Ordering::Acquire, Ordering::Relaxed),
        Ordering::Release => (Ordering::Relaxed, Ordering::Release),
        _ => panic!(),
    }
}
