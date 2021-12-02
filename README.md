# **Verifying Merge Sort in VST**
### Nils Lauermann ⦁ Advanced Coq Programming 2020

***

## **Compiling the project**

### Required Packages
* The Coq Proof Assistant, version 8.12.0 (October 2020)
* coq-vst 2.6
* coq-equations 1.2.3+8.12

### Build using the `make` command.

***

## **Project structure**

file                             | content
---------------------------------|---------
[msort.c](./msort.c)             | The C functions `msort` and  `merge` to be verified
[msort.v](./msort.v)             | The AST of the C file parsed by CompCert. It is not necessary to inspect this file as it is only used by VST for the verification
[Verif_msort.v](./Verif_msort.v) | The functional specification of `msort`/`merge` and the proofs that the C functions satisfy these specifications
[aux_lemmas.v](./aux_lemmas.v)   | Auxiliary Lemmas for the main proofs. These cover a wide area as this file includes lemmas for numbers but also many list facts used e.g. for the invariants are defined here

***

## **Design decisions**

### **The C functions**

As the trivial merge sort variant generally is not in place we have to have extra memory available. I considered a merge sort variant that only needs linear space but that would have complicated the `merge sort` function. Such an approach necessitates swapping the main and auxiliary array in alternation. In my experience verifying functions, that split and swap arrays a lot, is not always trivial. To accommodate the time constraints in this course I settled for the implementation that always allocates a new array for every merge.\
Let A be an array of size n. On every level of the merge/split tree we allocate exactly `n` memory cells. Considering we split the initial array exactly `log n` times we have overall additional memory of `O(n log n)`.


The `merge` function is defined in a way that it can be universally used in any merge sort implementation: In addition to the two arrays which are to be merged we also pass a pointer to the location where the result should be saved. This way we can easily exchange the `msort` function with a more memory friendly implementation.


### **`nat` vs `Z`**

In the verification of the functions I tried to use `nat` wherever possible (e.g. the current indices in the arrays during the loop in `merge`). This often involves conversion between `nat` and `Z` because VST obviously represents the C integers as numbers of type `Z` (in the range of int).\
This choice was purely personal preference. At first I only used values of type `Z` and that undoubtedly would have worked but I was more comfortable working with `nat`.\
I want to remark that this decision has no influence on the results as the elements in the array are unconstrained (signed) integers.
