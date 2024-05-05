// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use core::cell::Cell;
use core::mem::MaybeUninit;
use core::ptr::addr_of_mut;
use core::sync::atomic::{AtomicBool, Ordering};

use lilos::atomic::AtomicExt;
use lilos::spsc::{Popper, Pusher, Queue};

/// The easy case: a queue and its storage on the stack.
pub async fn test_stack() {
    let mut storage: [MaybeUninit<u8>; 5] = [MaybeUninit::uninit(); 5];
    let mut q = Queue::new(&mut storage);
    test_wherever(&mut q).await
}

/// Queue on stack, storage in a static, because maybe the storage is big and
/// you want to account for it at link time.
///
/// NOTE: this will only complete successfully once! The second attempt will
/// panic. This is a consequence of how I'm managing aliasing of the static
/// buffer below.
pub async fn test_static_storage() {
    static ONCE: AtomicBool = AtomicBool::new(false);
    assert!(!ONCE.swap_polyfill(true, Ordering::SeqCst));

    static mut STORAGE: [MaybeUninit<u8>; 5] = [MaybeUninit::uninit(); 5];
    let mut q = Queue::new(unsafe { &mut *addr_of_mut!(STORAGE) });
    test_wherever(&mut q).await
}

/// Queue *and* storage in a static, because this makes the resulting Push and
/// Pop have `'static` life, so they can be shared with an ISR.
///
/// NOTE: this will only complete successfully once! The second attempt will
/// panic. This is a consequence of how I'm managing aliasing of the static
/// buffer below.
pub async fn test_static_everything() {
    static ONCE: AtomicBool = AtomicBool::new(false);
    assert!(!ONCE.swap_polyfill(true, Ordering::SeqCst));

    static mut STORAGE: [MaybeUninit<u8>; 5] = [MaybeUninit::uninit(); 5];
    static mut Q: MaybeUninit<Queue<u8>> = MaybeUninit::uninit();
    let q = unsafe {
        let q = &mut *addr_of_mut!(Q);
        q.as_mut_ptr().write(Queue::new(&mut *addr_of_mut!(STORAGE)));
        &mut *q.as_mut_ptr()
    };
    test_wherever(q).await
}

/// Common implementation of spsc tests.
async fn test_wherever(q: &mut Queue<'_, u8>) {
    let (mut push, mut pop) = q.split();
    futures::join!(
        async {
            for i in 0..10 {
                push.reserve().await.push(i);
            }
        },
        async {
            for i in 0..10 {
                assert_eq!(pop.pop().await, i);
            }
        },
    );
}

/// If a Queue is dropped when non-empty, we expect to go through and Drop all
/// those elements. But do we?
pub async fn test_nonempty_drop() {
    let drops = Cell::new(0);

    struct NoticeDrop<'a>(&'a Cell<usize>);
    impl Drop for NoticeDrop<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    const N: usize = 5;

    // Safety: assume_init is safe if the resulting type doesn't assume
    // initialization, which an array of MaybeUninit does not.
    let mut storage: [MaybeUninit<_>; N + 1] = unsafe {
        MaybeUninit::uninit().assume_init()
    };

    let mut q = Queue::new(&mut storage);
    let (mut push, mut pop) = q.split();

    // Alright, record N things that notice when they are dropped:
    for _ in 0..N {
        push.reserve().await.push(NoticeDrop(&drops));
    }

    // nothing has been dropped yet:
    assert_eq!(drops.get(), 0);

    // We'll pop one manually just for the heck of it.
    let _ = pop.pop().await;
    assert_eq!(drops.get(), 1);

    // And then the rest:
    drop(q);
    assert_eq!(drops.get(), N);
}

/// This "test" just needs to compile, to verify that Push and Pop are indeed
/// Send as promised.
#[allow(dead_code)]
fn compile_test_send(push: Pusher<'_, u8>, pop: Popper<'_, u8>) {
    fn is_send<T: Send>(_: &T) {}
    is_send(&push);
    is_send(&pop);
}
