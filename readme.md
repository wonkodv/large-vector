Large Vector
============

Rust Vector for large amounts of data, that does not copy when growing, by using full `mmap`'d pages.

Maturity
--------

I made ths to learn about `mmap`.

This is a first draft, testing out my idea. I copied the doctests from
`alloc::vec::Vec` and they all pass.

I only have one test, where it grows until the virtual address changes , and data still look good.


Next Steps
----------

-   On shrinking, `madvise(MADV_FREE)`
-   Performance Test


Memory Use
----------

Creating huge vectors does not increase the memory usage immediately.
The following line only makes the OS assign 8GB of virtual address in the Process.

    let mut vec = LVec::<usize>::with_capacity(1024 * 1000 * 1000);

physical memory is only allocated when you actually use the page.

The same is true for `alloc::vec::Vec`, so it does not seem that this crate provides any benefit over standard vector.


License
-------

Licensed under either of

- Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0)

- MIT license (http://opensource.org/licenses/MIT)

at your option.
