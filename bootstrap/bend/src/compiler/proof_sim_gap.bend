# compiler: where Cir and the module could disagree
# =================================================
#
# Facts, by evaluation, at the two edges of the simulation:
#
# 1. A byte of output at address 2^32 - 1 (a limit of 65536 pages, next = P =
#    214748364 and outn = 15): Cir.exec.emit takes it (its check and
#    Cir.room pass), and so does the model's store8 since Wasm.fits takes an
#    end of exactly 2^32 in 65536 pages: the two agree.
# 2. A halt 0 with no output while the cells end past the memory (no cell
#    taken yet, the input's end just below a page's end): Cir gives
#    result{[]}, but the host's check of the output's place fails (trap). A
#    run of Mach.code never halts so (see the report of layer A).

import Base
import ./impl.bend as C

# 1: Cir's check of emit and its room pass at 20 × 214748364 + 15
def gap.emit.cir() -> {Bool.and(U32.is_lt(214748364, 214748365), U32.is_ge(U32.add(C.Cir.at(214748364), 15), 15)) == True{} : Bool}:
  {==}

def gap.emit.room() -> {C.Cir.room(U32.add(C.Cir.at(214748364), 15), 65536, 65536) == Some{65536} : Maybe<&2, U32>}:
  {==}

def gap.emit.at() -> {U32.add(C.Cir.at(214748364), 15) == 4294967295 : U32}:
  {==}

# 1: the model's store8 there is inside a memory of 65536 pages
def gap.emit.wasm() -> {C.Wasm.inside(65536, 4294967295, 0, 1) == True{} : Bool}:
  {==}

# 2: no book's cells, an input of 65516 bytes from byte 20: alloc gives one
# page, the first cell of the machine is 3277, whose first byte 65540 is past
# it
def gap.halt.pages() -> {C.Cir.alloc.pages(0, 65516, 1, 65536) == Some{1} : Maybe<&2, U32>}:
  {==}

def gap.halt.first() -> {C.Cir.first(0, U32.add(C.Cir.input.at(0), 65516)) == 3277 : U32}:
  {==}

# 2: the host's check of an empty output at 20 × 3277 fails in one page
def gap.halt.wasm() -> {C.Wasm.fits(1, C.Cir.at(3277), 0) == False{} : Bool}:
  {==}

# 2: and Cir gives result{[]} for halt{0}
def gap.halt.cir() -> {C.Cir.ended(C.Cir.Out.halt{0, C.Cir.State{[], C.Cir.Cells.none{}, 3277, 3277, 0, 1, 65536, [], [], 0}}) ==
  C.Wasm.Outcome.result{[]} : C.Wasm.Outcome}:
  {==}
