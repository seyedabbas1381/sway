library;

//! Defines the Sway core library prelude.
//! The prelude consists of implicitly available items,
//! for which `use` is not required.
use ::primitives::*;
use ::primitive_conversions::*;
use ::raw_ptr::*;
use ::raw_slice::*;
use ::never::*;
use ::ops::*;
use ::storage::*;
use ::str::*;
use ::codec::*;

pub fn decode_first_param<T>() -> T {
    let v = asm(size: __size_of::<T>(), ptr) {
        aloc size;
        move ptr hp;
        ptr: T
    };
    v
}
