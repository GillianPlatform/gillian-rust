# Notes about the memory model of MIR

## Understanding the Memory type from Interp

### The main map

Memory seems to be a map of the following form [defined here](https://doc.rust-lang.org/stable/nightly-rustc/rustc_mir/interpret/machine/trait.Machine.html#associatedtype.MemoryMap):

`AllocId -> MemoryKind * Allocation`

There's also additional data. But that looks like the main map.

##### AllocId

AllocId [defined here](https://doc.rust-lang.org/stable/nightly-rustc/rustc_mir/interpret/struct.AllocId.html) is just a unique id. I think it might correspond to GIL locations, unsure, this might be sub-optimal.

_Why did you write that Sacha?_ 

##### Memory Kind

[TYPE DEF](https://doc.rust-lang.org/stable/nightly-rustc/rustc_mir/interpret/memory/enum.MemoryKind.html)

Memory Kind is one of the following:

- `Stack` (can only be deallocated on stack pop)
- `VTable`, which seems to correspond to how dynamic dispatch is handled. Articles of interest are [this one about C++](https://pabloariasal.github.io/2017/06/10/understanding-virtual-tables/) and [this one about Rust](https://alschwalm.com/blog/static/2017/03/07/exploring-dynamic-dispatch-in-rust/). Cannot be deallocated. **Ok so that went away for some reason**
- `CallerLocation`, when it's allocated using the `caller_location` instrinsic. See [this link](https://doc.rust-lang.org/std/intrinsics/fn.caller_location.html). It has to do with the Location (i.e. code location `file:line:column`) of the function that called the current context. Used for panics, will probably require some kind of GIL trick.
- `Machine(T)`, i.e. a custom depending on the machine executing.

That MemoryKind raises the question: what's the default one ? Probably a machine-specific one ? I'd need to check what allocation of a vec does for example maybe ?

##### Allocation

It's the [following type](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir/interpret/struct.Allocation.html):

```rust
pub struct Allocation<Tag = (), Extra = ()> {
    bytes: Vec<u8, Global>,
    relocations: Relocations<Tag, AllocId>,
    init_mask: InitMask,
    pub size: Size,
    pub align: Align,
    pub mutability: Mutability,
    pub extra: Extra,
}
```

The first obvious note is the `bytes` field. The interpreter stores data as actual bytes. Gillian will probably need to abstract that like we did for CompCert. There's a not that says that the byte field only contains the offset in the case of pointers.
The `InitMask` denotes which part of the allocation is initialized.

The documentation for `relocations` is

> Maps from byte addresses to extra data for each pointer. Only the first byte of a pointer is inserted into the map; i.e., every entry in this map applies to `pointer_size` consecutive bytes starting at the given offset.

I don't exactly know what that means yet
after that, size, align, mutability & extra speak for themselves.

### Other info in the memory

`extra_fn_ptr` which is an additional pointer map specific to the machine. This could be used in Gillian for internal functions or maybe for

**More interesting**: `dead_alloc_map` keeps track of freed data:

> To be able to compare pointers with null, and to check alignment for accesses to ZSTs (where pointers may dangle), we keep track of the size even for allocations that do not exist any more.

Then, the memory also has a reference to the type context and additionnal info specific to the machine.



## The Place question:

- How are places and allocations linked ?

Places might just be expressions that evaluate "pointers", i.e. alloc ids & offsets. If that is true, then this cannot be our memory model. It is too low level. This should be our last resort memory model ?
Or maybe the right answer is to go the other way around ? Use the low-level memory model, and add optimisations when we can ?

Note that an allocation might actually be similar to a C block. Which is quite interesting, is there a different allocation id per object ? Per field ? How does that work ?

## Understanding simple MIR executions

### a.rs

```rust
fn main() {
    let x = 4;
    let z = x + 3;
}
```

```rust
// WARNING: This output format is intended for human consumers only
// and is subject to change without notice. Knock yourself out.
fn main() -> () {
    let mut _0: ();                      // return place in scope 0 at src/main.rs:2:11: 2:11
    let _1: i32;                         // in scope 0 at src/main.rs:3:9: 3:10
    scope 1 {
        debug x => _1;                   // in scope 1 at src/main.rs:3:9: 3:10
        let _2: i32;                     // in scope 1 at src/main.rs:4:9: 4:10
        scope 2 {
            debug z => _2;               // in scope 2 at src/main.rs:4:9: 4:10
        }
    }

    bb0: {
        _1 = const 4_i32;                // scope 0 at src/main.rs:3:13: 3:14
        _2 = const 7_i32;                // scope 1 at src/main.rs:4:13: 4:18
        return;                          // scope 0 at src/main.rs:5:2: 5:2
    }
}
```

So first of all, `_0` is Gillian's `ret` and `return` behaves similarly to Gillian's.
I think that unwinding and panicking might be modeled by gillian `ReturnError`.
Secondly, every value is correctly allocated, but some operations are optimised, e.g. const propagation.

Let's take a look at the generated MIR body debug.

```rust
Body {
    basic_blocks: [
        BasicBlockData {
            statements: [
								_1 = const 4_i32,
                _2 = const 7_i32,
                _0 = const (),
            ],
            terminator: Some(
                Terminator {
                    source_info: SourceInfo {
                        span: examples/a.rs:7:2: 7:2 (#0),
                        scope: scope[0],
                    },
                    kind: return,
                },
            ),
            is_cleanup: false,
        },
    ],
    phase: Optimization,
    source: MirSource {
        instance: Item(
            WithOptConstParam {
                did: DefId(0:7 ~ a[317d]::main),
                const_param_did: None,
            },
        ),
        promoted: None,
    },
    source_scopes: [
        SourceScopeData {
            span: examples/a.rs:4:1: 7:2 (#0),
            parent_scope: None,
            inlined: None,
            inlined_parent_scope: None,
            local_data: Set(
                SourceScopeLocalData {
                    lint_root: HirId {
                        owner: DefId(0:7 ~ a[317d]::main),
                        local_id: 0,
                    },
                    safety: Safe,
                },
            ),
        },
        SourceScopeData {
            span: examples/a.rs:5:5: 7:2 (#0),
            parent_scope: Some(
                scope[0],
            ),
            inlined: None,
            inlined_parent_scope: None,
            local_data: Set(
                SourceScopeLocalData {
                    lint_root: HirId {
                        owner: DefId(0:7 ~ a[317d]::main),
                        local_id: 0,
                    },
                    safety: Safe,
                },
            ),
        },
        SourceScopeData {
            span: examples/a.rs:6:5: 7:2 (#0),
            parent_scope: Some(
                scope[1],
            ),
            inlined: None,
            inlined_parent_scope: None,
            local_data: Set(
                SourceScopeLocalData {
                    lint_root: HirId {
                        owner: DefId(0:7 ~ a[317d]::main),
                        local_id: 0,
                    },
                    safety: Safe,
                },
            ),
        },
    ],
    generator: None,
    local_decls: [
        LocalDecl {
            mutability: Mut,
            local_info: None,
            internal: false,
            is_block_tail: None,
            ty: (),
            user_ty: None,
            source_info: SourceInfo {
                span: examples/a.rs:4:11: 4:11 (#0),
                scope: scope[0],
            },
        },
        LocalDecl {
            mutability: Not,
            local_info: Some(
                User(
                    Set(
                        Var(
                            VarBindingForm {
                                binding_mode: BindByValue(
                                    Not,
                                ),
                                opt_ty_info: None,
                                opt_match_place: Some(
                                    (
                                        None,
                                        examples/a.rs:5:13: 5:14 (#0),
                                    ),
                                ),
                                pat_span: examples/a.rs:5:9: 5:10 (#0),
                            },
                        ),
                    ),
                ),
            ),
            internal: false,
            is_block_tail: None,
            ty: i32,
            user_ty: None,
            source_info: SourceInfo {
                span: examples/a.rs:5:9: 5:10 (#0),
                scope: scope[0],
            },
        },
        LocalDecl {
            mutability: Not,
            local_info: Some(
                User(
                    Set(
                        Var(
                            VarBindingForm {
                                binding_mode: BindByValue(
                                    Not,
                                ),
                                opt_ty_info: None,
                                opt_match_place: Some(
                                    (
                                        None,
                                        examples/a.rs:6:13: 6:18 (#0),
                                    ),
                                ),
                                pat_span: examples/a.rs:6:9: 6:10 (#0),
                            },
                        ),
                    ),
                ),
            ),
            internal: false,
            is_block_tail: None,
            ty: i32,
            user_ty: None,
            source_info: SourceInfo {
                span: examples/a.rs:6:9: 6:10 (#0),
                scope: scope[1],
            },
        },
    ],
    user_type_annotations: [],
    arg_count: 0,
    spread_arg: None,
    var_debug_info: [
        VarDebugInfo {
            name: "x",
            source_info: SourceInfo {
                span: examples/a.rs:5:9: 5:10 (#0),
                scope: scope[1],
            },
            value: _1,
        },
        VarDebugInfo {
            name: "z",
            source_info: SourceInfo {
                span: examples/a.rs:6:9: 6:10 (#0),
                scope: scope[2],
            },
            value: _2,
        },
    ],
    span: examples/a.rs:4:1: 7:2 (#0),
    required_consts: [],
    is_polymorphic: false,
    predecessor_cache: PredecessorCache {
        cache: OnceCell(Uninit),
    },
    is_cyclic: GraphIsCyclicCache {
        cache: OnceCell(
            false,
        ),
    },
}
```



So unfortunately, this doesn't give much information.
I'd like to have more details about that particular statement for example:

```rust
_1 = const 4_i32
```

I'm guessing it is an [Assignment](https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/mir/enum.StatementKind.html#variant.Assign) 

```rust
Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>)
```

Where the [Place](https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/mir/struct.Place.html) is 

```rust
Place {
  local: 1,
  projection: []
}
```

And [Rvalue](https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/mir/enum.Rvalue.html) is

```rust
Use(Constant(Scalar(Int({ data= ?, size= ?}))))
```

^ I'm guessing there's also a userType indicating i32 ?
Fuck, there's a lot of variatns there, it's not really simple. Compilation is going to be hard.

Ok, let's try to find the case in the [eval_rvalue_into_place](https://doc.rust-lang.org/nightly/nightly-rustc/src/rustc_mir/interpret/step.rs.html#155) function.
The first thing we need to understand is what [`eval_place`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir/interpret/eval_context/struct.InterpCx.html#method.eval_place) is doing. What we want to understand more precisely is: what does a place evaluate to ? I think a place is an expression that evaluates to some kind of internal pointer. Is it a raw pointer ?

So, let's go through `eval_place`: 

```rust
pub struct Pointer<Tag = ()> {
    pub alloc_id: AllocId,
    pub offset: Size,
    pub tag: Tag,
}

pub struct Pointer<Tag = ()> {
    pub alloc_id: AllocId,
    pub offset: Size,
    pub tag: Tag,
}

pub enum Scalar<Tag = ()> {
    Int(ScalarInt), // Raw Int, oh shit
    Ptr(Pointer<Tag>), // Ok that's interesting
}

pub enum MemPlaceMeta<Tag = ()> {
    // Information required for the sound usage of a MemPlace. 
  	// So potentially, locations have metadata ?
    Meta(Scalar<Tag>),
    None,
    Poison,
}

pub struct MemPlace<Tag = ()> {
    pub ptr: Scalar<Tag>,
    pub align: Align, // alignment (power of 2)
    pub meta: MemPlaceMeta<Tag>,
}

pub enum Place<Tag = ()> {
    Ptr(MemPlace<Tag>),
       // AH: This is a location in memory. So either an actual loc,
       // or the ins of the main cell predicate.
    Local {
        frame: usize,
        local: Local,
    },
			// Locals are just local variables ! Corresponding exactly to GIL variables probably.
      // So sometimes it is actually possible to just read the variable, without accessing memory
}

pub struct PlaceTy<'tcx, Tag = ()> {
    place: Place<Tag>,
    pub layout: TyAndLayout<'tcx>, // let's not go into that for now
}

pub fn eval_place(
        &mut self,
        place: mir::Place<'tcx>,
    ) -> InterpResult<'tcx, PlaceTy<'tcx, M::PointerTag>> {
        let mut place_ty = PlaceTy {
            // This works even for dead/uninitialized locals; we check further when writing
            place: Place::Local { frame: self.frame_idx(), local: place.local },
            layout: self.layout_of_local(self.frame(), place.local, None)?,
        };

        for elem in place.projection.iter() {
            place_ty = self.place_projection(&place_ty, &elem)?
        }

        trace!("{:?}", self.dump_place(place_ty.place));
        // Sanity-check the type we ended up with.
        debug_assert!(mir_assign_valid_types(
            *self.tcx,
            self.param_env,
            self.layout_of(self.subst_from_current_frame_and_normalize_erasing_regions(
                place.ty(&self.frame().body.local_decls, *self.tcx).ty
            ))?,
            place_ty.layout,
        ));
        Ok(place_ty)
    }
```

Some links:
[MemPlace](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir/interpret/place/struct.MemPlace.html), [PlaceTy](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir/interpret/place/struct.PlaceTy.html), [Place](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir/interpret/place/enum.Place.html), [Scalar](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir/interpret/enum.Scalar.html), [Pointer](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir/interpret/struct.Pointer.html)

So here's what I've learned:

- A pointer is actually a loc-offset pair,  just like C. It also works the same.
- I don't have to use the same semantics as MIRI actually. The way Prusti does it is by [compiling places](https://github.com/viperproject/prusti-dev/blob/53096dad43e9ce7c9c45d3f4b1c6b062b57534e5/prusti-viper/src/encoder/mir_encoder/mod.rs#L70-L73) to [`PlaceEncoding`s](https://github.com/viperproject/prusti-dev/blob/master/prusti-viper/src/encoder/mir_encoder/place_encoding.rs#L21).

Here's the definition `PlaceEncoding` in Prusti:

```rust
pub enum PlaceEncoding<'tcx> {
    /// Just an expression, the most common case.
    Expr(vir::Expr),
    /// Field access expression
    FieldAccess {
        base: Box<PlaceEncoding<'tcx>>,
        field: vir::Field,
    },
    /// Array access expression
    ArrayAccess {
        base: Box<PlaceEncoding<'tcx>>,
        index: vir::Expr,
        encoded_elem_ty: vir::Type,
        rust_array_ty: ty::Ty<'tcx>,
    },
    Variant {
        base: Box<PlaceEncoding<'tcx>>,
        field: vir::Field,
    }
}
```

I'd need to undertand vir a tiny bit better. But basically, a place is most of the time an expression, or an access over a Field of another place encoding. The expression is most likely a variable name.



New question: What if there is no layout ? How is this resolved in MIRI ?
Nathan Chong answered this question: they make a choice. And therefore, it's obviously wrong, because they have compiler-specific choices. It is questionable whether or not it is ok to make assumptions about the layouts, but it is clearly wrong if you consider many targets for Rust, e.g. wasm.

# What's my memory model ?

Now comes the actually interesting question: what's my memory model ?
locals <=> variables
We need to do compcert-like magic on variables and field access. I'm thankful I have the C experience right now.
I also need a plan to handle weird accesses.
Let's look at that example again ?

![image-20210521235745969](/Users/sacha/Library/Application Support/typora-user-images/image-20210521235745969.png)

Ok so what do I need here ?
Slice : length and data are fields.
The most important question here is : `as_mut_ptr`
What's a pointer ? It's a thing that points to an address in memory, but given a memory model, it might NOT be loc + ofs, it might actually be loc + prop ?
What would be a spec of that ?

```rust
{ slice -> [alpha] * (mid == usize(#mid)) * (#mid < len(#alpha)) }
fn split_at_mut(slice: &mut [i32], mid: usize) -> (&mut [i32], &mut [i32])
{ (ret == (#a, #b)) * (#a -> [#beta]) * (#b -> [#gamma]) *
  (#alpha == #beta @ #gamma) * (len(#beta) = #mid) }
```

How to encode mutability ?
How to encode struct passing ? (the compcert trick ?)

ptr vs reference ?

How are we invalidating the data ?
Should I start replacing variables ?

### What are values ?

In the interpreter, values are either:

- Scalar (Pointer or Int) -> we also probably need things like bool ?

- Slices

- ByRef -> Most structs will be like that ?

  

## Compiling the control flow

The control flow of MIR works in bodies, basic blocs and terminators.
Supposedly, the control flow should only change with a bunch of terminators.

Now let's look at the [set of terminators](https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/mir/terminator/enum.TerminatorKind.html): 

- Goto: That one is trivial, we'll compile it to goto (done)
- SwitchInt: Switch on an operand depending on a value. This one is going to be the most intersting to handle.
  How much of that can I steal from RMC?
  Quite a lot I think. I can at least [steal that part of the code](https://github.com/model-checking/rmc/blob/main/compiler/rustc_codegen_rmc/src/codegen/statement.rs#L190)
- Resume: Unwinding should proceed, so a goto to the unwinding place.
- Abort: A fail? I don't really know.
- Return: Will probably be compiled to a return. (Done)
- Unreachable: This one should be a fail
- Drop: Drops the place.  That means there probably is an action call there, and a branching depending on how that goes.
- DropAndReplace: Drops the place and replace with a value. Same as above.
- Call: Several interesting things here:
  - It's can branch (unwind), that corresponds to a throw or whatever.
    We might leverage error mode in GIL.
  - There is a cleanup site in case something goes wrong.
    But then, do I specify anything there? If I want to specify my failure case but things get cleaned up?
    I could just use fail instead, not clean up, and leave it to the specification.
- Assert: Can fail, that's why it's a terminator
- Yield: Just another control flow. It is a bit unclear how the drop argument should be used.
- GenerateDrop: The end of dropping a generator (has to do with yield, that's to investigate)
- FalseEdge: A block where control flow can only ever take one path but borrowchecker needs to be more conservative. It's basically a simple goto, and the `imaginary_target` should be ignored.
- FalseUnwind: Probably the same as FalseEdge for our use-case.
- InlineAsm: For now, die in hell.



Ok so, am I missing anything in the definiton of bodies to start implementing?

Here are some type definitions:

```rust
pub struct Body<'tcx> {

    basic_blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>, // Simple map function should work here
    pub phase: MirPhase, // Ignore for now
    pub source: MirSource<'tcx>, // Ignore for now
    pub source_scopes: IndexVec<SourceScope, SourceScopeData<'tcx>>, // That should be passed in some kind of body context. Used for debugging, annotation etc..
    pub generator: Option<Box<GeneratorInfo<'tcx>>>, // If that is not None, panic! for now
    pub local_decls: LocalDecls<'tcx>, // The first one is the return, arg_count arguments, then any user_declared/temporary variable. They should probably be initialized to undefined at the beggining of the proc.
    pub user_type_annotations: CanonicalUserTypeAnnotations<'tcx>, // I don't know how to use that yet.
    pub arg_count: usize, // see local_decls
    pub spread_arg: Option<Local>, // If that is not None, panic! for now
    pub var_debug_info: Vec<VarDebugInfo<'tcx>>, // That should be passed in some kind of body context.
    pub span: Span, // Useless, more span in the rest?
    pub required_consts: Vec<Constant<'tcx>>, // For now, panic! if that is not empty
    pub is_polymorphic: bool, // For now, panic! if that is true.
    predecessor_cache: PredecessorCache, // I don't think that is useful for us
    is_cyclic: GraphIsCyclicCache, // I don't think that is useful for us, we'll see when we get to invariants.
}


```







# Ownership : Move and Copy

One very important question is: what does move mean, what does copy mean?
Take the following example of Rust program

```rust
fn test(u: A, v: A) {
  let x : (A, A) = (u, v);
  let x.0 = x.1;
}

```

First of all, in this argument, I'll assume that the memory is some kind of tree.
I built a pair in memory, that's a block, which looks like this.

```
         l
        / \       We'll call this memory M.
       u   v
```

Now the question is: when the move is happening on the second line of the function, is only the store changing?

There are two interpretations. The first on is this

```rust
fn test(u: A, v: A) {
  let x : (A, A) = (u, v); // memory is M, store is (x -> (l.0, l.1))
  let x.0 = x.1; // memory is M, store is (x -> (l.1, nono))
}
```

The second one is this:

```rust
fn test(u: A, v: A) {
  let x : (A, A) = (u, v); // memory is M, store is (x -> (l, [])), i.e. x is the pointer to l with an empty proj
  let x.0 = x.1; // memory is M', store is (x -> (l, [])), i.e. the memory has changed and x hasn't.
}

// With M' being the following memory
//         l
//        / \       
//       v  nono
```

One thing that would help settle this is: what happens to a moved value? Is it still guaranteed to be in memory until the end of the scope? What if I have a raw pointer to it?

Well, it turns out that a raw pointer pointing to a variable that is not live anymore is not valid.
So the MEMORY itself has been moved.

So here's an attempt at memory model:

```ocaml
type action =
	| Load of Loc.t * Proj.t * Typ.t * bool (** Location, projection, type and true if the value is moved *)
	| Store of Loc.t * Proj.t * Typ.t * Val.t
	| Free of Loc.t (** How do you assert that the whole block is there and the projection is empty? *)
	| Alloc of Typ.t (** How do you write that this is the root of the tree? Same problem)
```





# Type Encodings

Here we're going to talk about type encodings. How is each type encoded in GIL?

## Numeric types

Numerical values are directly encoded as Gillian numerical values. We use integers and therefore, this is going to require some heavy work inside Gillian.

## Tuples

Tuples are encoded as GIL lists. Although, unfortunately, it might be difficult to get that from the MIR...

Here's a simple function, and the corresponding mir body:

```rust
pub fn test() {
    let mut x = ((1, 2), (3, 4, (5, 6)));
    x.1 .2 .0 = 12;
}

// MIR BODY - READABLE
fn test() -> () {
    let mut _0: ();                      
    let mut _1: ((i32, i32), (i32, i32, (i32, i32))); 
    let mut _2: (i32, i32, (i32, i32));  
    scope 1 {
        debug x => _1;                   
    }

    bb0: {
        (_2.0: i32) = const 3_i32;
        (_2.1: i32) = const 4_i32;
        (_2.2: (i32, i32)) = const (5_i32, 6_i32);
        (_1.0: (i32, i32)) = const (1_i32, 2_i32);
        (_1.1: (i32, i32, (i32, i32))) = move _2;
        (((_1.1: (i32, i32, (i32, i32))).2: (i32, i32)).0: i32) = const 12_i32;
        return;
    }
}

// MIR BODY - DEBUG
test : Body {
    basic_blocks: [
        BasicBlockData {
            statements: [
                (_2.0: i32) = const 3_i32,
                (_2.1: i32) = const 4_i32,
                (_2.2: (i32, i32)) = const (5_i32, 6_i32),
                (_1.0: (i32, i32)) = const (1_i32, 2_i32),
                (_1.1: (i32, i32, (i32, i32))) = move _2,
                (((_1.1: (i32, i32, (i32, i32))).2: (i32, i32)).0: i32) = const 12_i32,
            ],
            terminator: Some(
                Terminator {
                    source_info: SourceInfo {
                        span: examples/store_tuples.rs:7:2: 7:2 (#0),
                        scope: scope[0],
                    },
                    kind: return,
                },
            ),
            is_cleanup: false,
        },
    ],
    phase: Optimization,
    source: MirSource {
        instance: Item(
            WithOptConstParam {
                did: DefId(0:7 ~ store_tuples[a9f3]::test),
                const_param_did: None,
            },
        ),
        promoted: None,
    },
    source_scopes: [
        SourceScopeData {
            span: examples/store_tuples.rs:4:1: 7:2 (#0),
            parent_scope: None,
            inlined: None,
            inlined_parent_scope: None,
            local_data: Set(
                SourceScopeLocalData {
                    lint_root: HirId {
                        owner: DefId(0:7 ~ store_tuples[a9f3]::test),
                        local_id: 0,
                    },
                    safety: Safe,
                },
            ),
        },
        SourceScopeData {
            span: examples/store_tuples.rs:5:5: 7:2 (#0),
            parent_scope: Some(
                scope[0],
            ),
            inlined: None,
            inlined_parent_scope: None,
            local_data: Set(
                SourceScopeLocalData {
                    lint_root: HirId {
                        owner: DefId(0:7 ~ store_tuples[a9f3]::test),
                        local_id: 0,
                    },
                    safety: Safe,
                },
            ),
        },
    ],
    generator: None,
    local_decls: [
        LocalDecl {
            mutability: Mut,
            local_info: None,
            internal: false,
            is_block_tail: None,
            ty: (),
            user_ty: None,
            source_info: SourceInfo {
                span: examples/store_tuples.rs:4:15: 4:15 (#0),
                scope: scope[0],
            },
        },
        LocalDecl {
            mutability: Mut,
            local_info: Some(
                User(
                    Set(
                        Var(
                            VarBindingForm {
                                binding_mode: BindByValue(
                                    Mut,
                                ),
                                opt_ty_info: None,
                                opt_match_place: Some(
                                    (
                                        None,
                                        examples/store_tuples.rs:5:17: 5:41 (#0),
                                    ),
                                ),
                                pat_span: examples/store_tuples.rs:5:9: 5:14 (#0),
                            },
                        ),
                    ),
                ),
            ),
            internal: false,
            is_block_tail: None,
            ty: ((i32, i32), (i32, i32, (i32, i32))),
            user_ty: None,
            source_info: SourceInfo {
                span: examples/store_tuples.rs:5:9: 5:14 (#0),
                scope: scope[0],
            },
        },
        LocalDecl {
            mutability: Mut,
            local_info: None,
            internal: false,
            is_block_tail: None,
            ty: (i32, i32, (i32, i32)),
            user_ty: None,
            source_info: SourceInfo {
                span: examples/store_tuples.rs:5:26: 5:40 (#0),
                scope: scope[0],
            },
        },
    ],
    user_type_annotations: [],
    arg_count: 0,
    spread_arg: None,
    var_debug_info: [
        VarDebugInfo {
            name: "x",
            source_info: SourceInfo {
                span: examples/store_tuples.rs:5:9: 5:14 (#0),
                scope: scope[1],
            },
            value: _1,
        },
    ],
    span: examples/store_tuples.rs:4:1: 7:2 (#0),
    required_consts: [],
    is_polymorphic: false,
    predecessor_cache: PredecessorCache {
        cache: OnceCell(Uninit),
    },
    is_cyclic: GraphIsCyclicCache {
        cache: OnceCell(
            false,
        ),
    },
}
```



This is tricky, because of what the constant tuples look like as values:

```rust
// In this
(_2.2: (i32, i32)) = const (5_i32, 6_i32);

// The const value is this
ByRef {
    alloc: Allocation {
        bytes: [
            5,
            0,
            0,
            0,
            6,
            0,
            0,
            0,
        ],
        relocations: Relocations(
            SortedMap {
                data: [],
            },
        ),
        init_mask: InitMask {
            blocks: [
                255,
            ],
            len: Size {
                raw: 8,
            },
        },
        align: Align {
            pow2: 2,
        },
        mutability: Not,
        extra: (),
    },
    offset: Size {
        raw: 0,
    },
}
// That is upsetting, because it is at the byte level and I don't really want that.
// Or do I?
```



## References

Ok so what about dereference and reference?

How does one handle that?

```rust
// THE RUST

pub fn add_four(x: &i32) -> i32 {
    (*x) + 4
}

pub fn test() {
    let z = 4;
    let _y = add_four(&z);
}

// THE MIR

fn add_four(_1: &i32) -> i32 {
    debug x => _1;                       
    let mut _0: i32;   
    let mut _2: i32;  
    let mut _3: (i32, bool);             

    bb0: {
        _2 = (*_1);                      
        _3 = CheckedAdd(_2, const 4_i32); 
        assert(!move (_3.1: bool), "attempt to compute `{} + {}`, which would overflow", move _2, const 4_i32) -> bb1; 
    }

    bb1: {
        _0 = move (_3.0: i32);        
        return;                       
    }
}

fn test() -> () {
    let mut _0: ();                
    let     _1: i32;                      
    let mut _3: &i32;                   
    let     _4: &i32;                      
    scope 1 {
        debug z => _1;                 
        let _2: i32;                  
        scope 2 {
            debug _y => _2;            
        }
    }

    bb0: {
        _1 = const 4_i32;                
        _4 = &_1;                        
        _3 = _4;                         
        _2 = add_four(move _3) -> bb1;  
    }

    bb1: {
        return;  
    }
}

// THE GIL WE WANT

proc add_four(x) {
  ret := undefined; // No allocation, unit is zero-sized.
  mir__temp_2 := undefined;
  mir__temp_3 := {{ undefined, undefined }};
  
}

proc test() {
  ret := null;
  mir__temp_2 := undefined;
  mir__temp_3 := {{ undefined, undefined }};
  
  

```



# Notes now that I started the compiler

### The discriminant Rvalue in MIR:

> Discriminant: Undefined (i.e., no effort is made to make it defined, but there’s no reason why it cannot be defined to return, say, a 0) if ADT is not an enum. 

So is it defined or not?

### Copy vs Move

In this program, it is unclear wether undefined behaviour is happening or not:

```rust
#![no_std]
struct A {
    v: i32,
}

fn test(u: A, v: A) -> i32 {
    let mut x: (A, A) = (u, v);
    let sec: *const A = &x.1;
    x.0 = x.1;
    unsafe { (*sec).v }
}

pub fn main() {
    let u: A = A { v: 1 };
    let v: A = A { v: 2 };
    let _ret = test(u, v);
}
```

I.e. is `move` deinitializing memory or not?

### Semantics of enum manipulation?

In particular, what does a downcast mean? How to serialize them?



# Notes from the meeting with Nathan

https://github.com/firecracker-microvm/firecracker -> No use of std almost
https://cve.mitre.org/cgi-bin/cvename.cgi?name=CVE-2019-18960
https://github.com/model-checking/rmc
https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS/Test/VeriFast