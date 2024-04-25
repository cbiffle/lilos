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
    fn swap_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value;

    /// If `self`'s value is equal to `current`, atomically replace it with
    /// `new`, otherwise leave it untouched.
    ///
    /// Returns `Ok(current)` on success, `Err(actual_value)` on failure.
    fn compare_exchange_polyfill(&self, current: Self::Value, new: Self::Value, success: Ordering, failure: Ordering) -> Result<Self::Value, Self::Value>;
}

/// Atomic operations that apply to arithmetic types.
pub trait AtomicArithExt: AtomicExt {
    /// Atomically add `val` to our contents, returning the original value.
    fn fetch_add_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value;
    /// Atomically OR `val` into our contents, returning the original value.
    fn fetch_or_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value;
}

#[cfg(feature = "has-native-rmw")]
impl AtomicExt for AtomicU32 {
    type Value = u32;

    fn swap_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        self.swap(val, ordering)
    }
    fn compare_exchange_polyfill(&self, current: Self::Value, new: Self::Value, success: Ordering, failure: Ordering) -> Result<Self::Value, Self::Value> {
        self.compare_exchange(current, new, success, failure)
    }
}

#[cfg(feature = "has-native-rmw")]
impl AtomicArithExt for AtomicU32 {
    fn fetch_add_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        self.fetch_add(val, ordering)
    }
    fn fetch_or_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        self.fetch_or(val, ordering)
    }
}

#[cfg(feature = "has-native-rmw")]
impl AtomicExt for AtomicUsize {
    type Value = usize;

    fn swap_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        self.swap(val, ordering)
    }
    fn compare_exchange_polyfill(&self, current: Self::Value, new: Self::Value, success: Ordering, failure: Ordering) -> Result<Self::Value, Self::Value> {
        self.compare_exchange(current, new, success, failure)
    }
}

#[cfg(feature = "has-native-rmw")]
impl AtomicArithExt for AtomicUsize {
    fn fetch_add_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        self.fetch_add(val, ordering)
    }
    fn fetch_or_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        self.fetch_or(val, ordering)
    }
}

#[cfg(feature = "has-native-rmw")]
impl<T> AtomicExt for AtomicPtr<T> {
    type Value = *mut T;

    fn swap_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        self.swap(val, ordering)
    }
    fn compare_exchange_polyfill(&self, current: Self::Value, new: Self::Value, success: Ordering, failure: Ordering) -> Result<Self::Value, Self::Value> {
        self.compare_exchange(current, new, success, failure)
    }
}

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

#[cfg(not(feature = "has-native-rmw"))]
impl<T> AtomicExt for AtomicPtr<T> {
    type Value = *mut T;

    fn swap_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        let (lo, so) = rmw_ordering(ordering);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            self.store(val, so);
            x
        })
    }
    fn compare_exchange_polyfill(&self, current: Self::Value, new: Self::Value, success: Ordering, failure: Ordering) -> Result<Self::Value, Self::Value> {
        let (lo, so) = rmw_ordering(success);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            if x == current {
                self.store(new, so);
                break Ok(x);
            } else {
                break Err(x);
            }
        });
    }
}

#[cfg(not(feature = "has-native-rmw"))]
impl AtomicExt for AtomicU32 {
    type Value = u32;

    #[inline(always)]
    fn swap_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        let (lo, so) = rmw_ordering(ordering);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            self.store(val, so);
            x
        })
    }
    fn compare_exchange_polyfill(&self, current: Self::Value, new: Self::Value, success: Ordering, failure: Ordering) -> Result<Self::Value, Self::Value> {
        let (lo, so) = rmw_ordering(success);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            if x == current {
                self.store(new, so);
                break Ok(x);
            } else {
                break Err(x);
            }
        });
    }
}

#[cfg(not(feature = "has-native-rmw"))]
impl AtomicArithExt for AtomicU32 {
    #[inline(always)]
    fn fetch_add_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        let (lo, so) = rmw_ordering(ordering);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            self.store(x.wrapping_add(val), so);
            x
        })
    }

    #[inline(always)]
    fn fetch_or_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        let (lo, so) = rmw_ordering(ordering);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            self.store(x | val, so);
            x
        })
    }
}

#[cfg(not(feature = "has-native-rmw"))]
impl AtomicExt for AtomicUsize {
    type Value = usize;

    #[inline(always)]
    fn swap_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        let (lo, so) = rmw_ordering(ordering);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            self.store(val, so);
            x
        })
    }
    fn compare_exchange_polyfill(&self, current: Self::Value, new: Self::Value, success: Ordering, failure: Ordering) -> Result<Self::Value, Self::Value> {
        let (lo, so) = rmw_ordering(success);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            if x == current {
                self.store(new, so);
                break Ok(x);
            } else {
                break Err(x);
            }
        });
    }
}

#[cfg(not(feature = "has-native-rmw"))]
impl AtomicArithExt for AtomicUsize {
    #[inline(always)]
    fn fetch_add_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        let (lo, so) = rmw_ordering(ordering);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            self.store(x.wrapping_add(val), so);
            x
        })
    }

    #[inline(always)]
    fn fetch_or_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        let (lo, so) = rmw_ordering(ordering);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            self.store(x | val, so);
            x
        })
    }
}

#[cfg(feature = "has-native-rmw")]
impl AtomicExt for AtomicBool {
    type Value = bool;

    fn swap_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        self.swap(val, ordering)
    }
    fn compare_exchange_polyfill(&self, current: Self::Value, new: Self::Value, success: Ordering, failure: Ordering) -> Result<Self::Value, Self::Value> {
        self.compare_exchange(current, new, success, failure)
    }
}

#[cfg(not(feature = "has-native-rmw"))]
impl AtomicExt for AtomicBool {
    type Value = bool;

    #[inline(always)]
    fn swap_polyfill(&self, val: Self::Value, ordering: Ordering) -> Self::Value {
        let (lo, so) = rmw_ordering(ordering);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            self.store(val, so);
            x
        })
    }
    fn compare_exchange_polyfill(&self, current: Self::Value, new: Self::Value, success: Ordering, failure: Ordering) -> Result<Self::Value, Self::Value> {
        let (lo, so) = rmw_ordering(success);
        cortex_m::interrupt::free(|_| {
            let x = self.load(lo);
            if x == current {
                self.store(new, so);
                break Ok(x);
            } else {
                break Err(x);
            }
        });
    }
}
