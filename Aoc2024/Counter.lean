import Std.Data.HashMap.Basic 

abbrev Counter α [BEq α] [Hashable α] := Std.HashMap α Nat

namespace Counter

def add {α} [BEq α] [Hashable α] (counter : Counter α) (a : α) (c : Nat) :=
  counter.alter a (some <| ·.getD 0 + c)

def total {α} [BEq α] [Hashable α] (counter : Counter α) : Nat :=
  counter.values.sum

def ofList {α} [BEq α] [Hashable α] (xs : List α) : Counter α :=
  xs.foldr (fun a acc => Counter.add acc a 1) Std.HashMap.empty

end Counter 
