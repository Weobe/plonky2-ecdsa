#![allow(clippy::needless_range_loop)]
#![feature(get_many_mut)]
#![feature(trait_alias)]
//#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub mod curve;
pub mod field;
pub mod gadgets;
pub mod gates;