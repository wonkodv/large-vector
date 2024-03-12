Large Vector
============

Rust Vector for large amounts of data, that does not copy when growing, by using full `mmap`'d pages.

Maturity
--------

This is a first draft, testing out my idea. I copied the doctests from
`alloc::vec::Vec` and they all pass.

I only have one test, where it grows until the virtual address changes , and data still look good.


Next Steps
----------

-   Implement a version with fallible grow, that does not relocate (no MREMAP_MAYMOVE),  and can hand out
    `Pin<T>`. 
-   Find out if this has been done before
-   Get someone to review this




License
-------

Licensed under either of

- Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0)

- MIT license (http://opensource.org/licenses/MIT)

at your option.
