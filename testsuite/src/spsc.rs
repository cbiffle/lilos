use core::mem::MaybeUninit;
use core::ptr::addr_of_mut;

use lilos::reexport::portable_atomic::{AtomicBool, Ordering};

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
    assert!(!ONCE.swap(true, Ordering::SeqCst));

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
    assert!(!ONCE.swap(true, Ordering::SeqCst));

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

/// This "test" just needs to compile, to verify that Push and Pop are indeed
/// Send as promised.
#[allow(dead_code)]
fn compile_test_send(push: Pusher<'_, u8>, pop: Popper<'_, u8>) {
    fn is_send<T: Send>(_: &T) {}
    is_send(&push);
    is_send(&pop);
}
