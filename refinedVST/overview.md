This folder contains progress towards reimplementing [RefinedC](https://gitlab.mpi-sws.org/iris/refinedc/-/tree/master) on VST.

The main tasks are:
1. Extend the Clight parser (`clightgen`) to recognize RefinedC [annotations](https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/ANNOTATIONS.md), or else write a converter from RefinedC ASTs to Clight ASTs
2. Port some or all of Lithium ([lithium](https://gitlab.mpi-sws.org/iris/refinedc/-/tree/master/theories/lithium) folder in RefinedC) to be generic in the type of proposition instead of using `iProp`, or where that is impossible, port it to use ORA props/`assert`s
3. Port the implementation of RefinedC's type system ([typing](https://gitlab.mpi-sws.org/iris/refinedc/-/tree/master/theories/typing) folder in RefinedC) to VST's logic, and re-prove its typing rules.
