This folder contains progress towards reimplementing [RefinedC](https://gitlab.mpi-sws.org/iris/refinedc/-/tree/master) on VST.

RefinedC is
1. their types (defined in [type.v](./typing/type.v)) about points-tos
2. typing rules designed for automated reasoning
. We define similar types for Clight points-tos and recover typing rules.

The main tasks are:
1. Extend the Clight parser (`clightgen`) to recognize RefinedC [annotations](https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/ANNOTATIONS.md), or else write a converter from RefinedC ASTs to Clight ASTs
2. Port some or all of Lithium ([lithium](https://gitlab.mpi-sws.org/iris/refinedc/-/tree/master/theories/lithium) folder in RefinedC) to be generic in the type of proposition instead of using `iProp`, or where that is impossible, port it to use ORA props/`assert`s
3. Port the implementation of RefinedC's type system ([typing](https://gitlab.mpi-sws.org/iris/refinedc/-/tree/master/theories/typing) folder in RefinedC) to VST's logic, and re-prove its typing rules.

### Typing
Prereq: RefinedC Paper

This section notes some differences between RefinedC and refinedVST about definitions of `mapsto` and `type` in [type.v](./typing/type.v).

RefinedC is built for the Caesium C semantics, a [`mapsto`](https://gitlab.mpi-sws.org/iris/refinedc/-/blob/3aa46835a59adb4b0a83b6ef94e0c4dc9ba19c43/theories/caesium/ghost_state.v#L147) is defined as owning a list of bytes; separately, a [`layout`](https://gitlab.mpi-sws.org/iris/refinedc/-/blob/3aa46835a59adb4b0a83b6ef94e0c4dc9ba19c43/theories/caesium/layout.v#L5) describes the size and alignment used for interpreting this list of bytes. For more complex data structures, fancier layouts are defined (e.g. [`struct_layout`](https://gitlab.mpi-sws.org/iris/refinedc/-/blob/3aa46835a59adb4b0a83b6ef94e0c4dc9ba19c43/theories/caesium/layout.v)).

VST has different layers of mapstos, we currently choose [`data_at_rec`](../floyd/data_at_rec_lemmas.v) as the VST's equivalent of RefinedC's mapsto because we want a single mapsto to be able to hold the value of an entire aggregated data structure. Then the equivalent of RefinedC's `layout` is roughly [`Ctypes.type`](../compcert/cfrontend/Ctypes.v), and we define `has_layout_val v_rep cty := value_fits cty v ∧ type_is_volatile cty = false`. It contains `type_is_volatile cty = false` so that `has_layout_val v_rep cty -> tc_val' v_rep cty` for non-aggregated data types (by `value_fits_eq`), and `tc_val'`  is useful for [`wp` tactics](../veric/lifting.v) for exection in VeriC.

A consequence of using `reptype cty` as the equivalent of `val` means assertions that use this directly or indirectly needs `cty` as an argument, which usually comes from `typeof e` where `e` is an expression that evaluates to the value.  

| RefinedVST                                      | RefinedC                              |
| ----------------------------------------------- | ------------------------------------- |
| data_at_rec                                     | mapsto                                |
| [`Ctypes.type`](../compcert/cfrontend/Ctypes.v) | layout                                |
| reptype (cty:Ctypes.type)                       | val                                   |
| has_layout_val cty: reptype cty -> Prop         | has_layout_val: val -> layout -> Prop |
| has_layout_loc: val -> Prop                     | has_layout_loc: val -> Prop           |
