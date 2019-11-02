//! A simple operating system based around futures.

#![no_std]
#![feature(never_type)]

#[macro_use] pub mod list;
pub mod time;
pub mod exec;
pub mod mutex;
