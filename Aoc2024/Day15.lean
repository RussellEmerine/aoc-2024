import Std.Data.HashSet.Basic 
import «Aoc2024».Util.GridArray

namespace Day15

inductive Cell
| None
| Item -- either a box or the robot 
| Wall
deriving DecidableEq 

structure Warehouse (m n : Nat) where
  grid : GridArray m n Cell
  robot : Idx m n

namespace Warehouse

def ofLines (lines : Array String) :
    Except String ((m : Nat) × (n : Nat) × Warehouse m n × Array Direction) := do
  let mut gridlines : Array (Array Cell) := #[]
  let mut in_grid := true
  let mut moves := #[]
  -- apparently you can't shadow mutables 
  let mut robot' := none 
  for (line, i) in lines.zipWithIndex do
    if line = "" then
      in_grid := false
    else if in_grid then
      if let some j := line.toList.indexOf? '@' then
        robot' := some (i, j)
      let cells ← line.toList.toArray.mapM fun
        | '.' => Except.ok Cell.None
        | 'O' | '@' => Except.ok Cell.Item
        | '#' => Except.ok Cell.Wall
        | _ => Except.error "invalid character in warehouse grid"
      gridlines := gridlines.push cells 
    else
      let dirs ← line.toList.toArray.mapM fun 
        | '^' => Except.ok Direction.U
        | '>' => Except.ok Direction.R
        | 'v' => Except.ok Direction.D
        | '<' => Except.ok Direction.L
        | _ => Except.error "invalid character in movement sequence"
      moves := moves ++ dirs
  let ⟨m, n, grid⟩ ← GridArray.ofLines gridlines
  let robot ← robot'.elim (Except.error "no robot found") Except.ok 
  let robot ← if h : robot.fst < m ∧ robot.snd < n then
      Except.ok (⟨robot.fst, h.left⟩, ⟨robot.snd, h.right⟩)
    else
      Except.error "robot out of bounds"
  return ⟨m, n, { grid, robot }, moves⟩

-- double it: only the *left* side of the box is recorded
def double (w : Warehouse m n) : Warehouse m (2 * n) where
  grid := GridArray.ofFn fun i j =>
    match w.grid.get (i, ⟨j.val / 2, Nat.div_lt_of_lt_mul j.is_lt⟩) with
    | .None => Cell.None
    | .Wall => Cell.Wall
    | .Item => if Even j.val then Cell.Item else Cell.None
  robot := (w.robot.fst, ⟨w.robot.snd.val * 2, by
    rw [mul_comm, Nat.mul_lt_mul_left]
    exact w.robot.snd.is_lt
    exact zero_lt_two⟩)

def nextSpace (w : Warehouse m n) (p : Idx m n) (d : Direction) : Nat → Option (Idx m n)
| 0 => none
| (fuel + 1) =>
  match w.grid.get p with 
  | .Item => do nextSpace w (← p.move d) d fuel
  | .None => some p
  | .Wall => none 

def move (w : Warehouse m n) (d : Direction) : Warehouse m n :=
  if let (some p, some robot) := (w.nextSpace w.robot d (m + n), w.robot.move d) then 
    let grid := w.grid.set p Cell.Item
    let grid := grid.set w.robot Cell.None
    { grid, robot }
  else
    w

def nextSpaceDoubledVertical 
  (w : Warehouse m n)
  (layer : Array (Idx m n))
  (acc : Array (Idx m n))
  (d : Direction) :
    Nat → Option (Array (Idx m n))
| 0 => none
| fuel + 1 => do
  let () ← guard <| layer.all fun p =>
    [p.move d, (p.move d).bind (·.move Direction.R)].reduceOption.all (w.grid.get · ≠ Cell.Wall)
  let next := layer.toList.filterMap (·.move d)
    |>.flatMap (fun p => [p.move Direction.L, some p, p.move Direction.R])
    |>.reduceOption
    |>.filter (w.grid.get · = Cell.Item)
    |> Std.HashSet.ofList
    |>.toArray
  if next.isEmpty then
    return acc ++ layer 
  else 
    nextSpaceDoubledVertical w next (acc ++ layer) d fuel

def nextSpaceDoubledL
  (w : Warehouse m n)
  (p : Idx m n)
  (acc : Array (Idx m n)) :
    Nat → Option (Array (Idx m n))
| 0 => none
| fuel + 1 => 
  if (p.move .L).any (w.grid.get · = Cell.Wall) then
    none
  else if let some p' := (((p.move .L).bind (·.move .L)).filter (w.grid.get · = Cell.Item)) then
    nextSpaceDoubledL w p' (acc.push p) fuel
  else
    some (acc.push p)

def nextSpaceDoubledR
  (w : Warehouse m n)
  (p : Idx m n)
  (acc : Array (Idx m n)) :
    Nat → Option (Array (Idx m n))
| 0 => none
| fuel + 1 => 
  if ((p.move .R).bind (·.move .R)).any (w.grid.get · = Cell.Wall) then
    none
  else if let some p' := ((p.move .R).bind (·.move .R)).filter (w.grid.get · = Cell.Item) then
    nextSpaceDoubledR w p' (acc.push p) fuel
  else
    some (acc.push p)

def nextSpaceDoubled (w : Warehouse m n) (p : Idx m n) (d : Direction) :
    Option (Array (Idx m n)) :=
  match d with
  | .U | .D =>
    if (p.move d).any (w.grid.get · = .Wall) then
      none 
    else
      let ps := [p.move d, (p.move d).bind (·.move .L)]
        |>.reduceOption
        |>.filter (w.grid.get · = .Item)
        |>.toArray 
      nextSpaceDoubledVertical w ps #[p] d (m + n)
  | .L => nextSpaceDoubledL w p #[] (m + n)
  | .R =>
    if (p.move .R).any (w.grid.get · = .Wall) then
      none
    else if let some p' := (p.move .R).filter (w.grid.get · = .Item) then 
      nextSpaceDoubledR w p' #[p] (m + n)
    else
      some #[p]

def moveDoubled (w : Warehouse m n) (d : Direction) : Warehouse m n := Id.run <| do
  if let (some ps, some robot) := (w.nextSpaceDoubled w.robot d, w.robot.move d) then
    let mut grid := w.grid
    for p in ps do
      grid := grid.set p Cell.None
    for p in ps.filterMap (·.move d) do
      grid := grid.set p Cell.Item 
    { grid, robot }
  else
    w

def gps (p : Idx m n) : Nat := p.fst.val * 100 + p.snd.val 

def gpsSum (w : Warehouse m n) : Nat :=
  (· - gps w.robot) <| GridArray.indices m n
    |>.filter (w.grid.get · = Cell.Item)
    |>.map gps
    |>.sum 

instance : ToString (Warehouse m n) where
  toString w := "\n".intercalate <| List.finRange m
    |>.map (w.grid.row ·
      |>.map (fun | .None => '.' | .Wall => '#' | .Item => 'O')
      |>.toList
      |> String.mk)

end Warehouse 

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day15/test.txt")
  let ⟨_, _, w, moves⟩ ← IO.ofExcept (Warehouse.ofLines lines)
  println! "Test: {moves.foldl Warehouse.move w |>.gpsSum}"
  println! "Expected: {10092}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day15/task.txt")
  let ⟨_, _, w, moves⟩ ← IO.ofExcept (Warehouse.ofLines lines)
  println! "Test: {moves.foldl Warehouse.move w |>.gpsSum}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day15/test.txt")
  let ⟨_, _, w, moves⟩ ← IO.ofExcept (Warehouse.ofLines lines)
  println! "Test: {moves.foldl Warehouse.moveDoubled w.double |>.gpsSum}"
  println! "Expected: {9021}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day15/task.txt")
  let ⟨_, _, w, moves⟩ ← IO.ofExcept (Warehouse.ofLines lines)
  println! "Test: {moves.foldl Warehouse.moveDoubled w.double |>.gpsSum}"

end Task2

def main : IO Unit := do
  println! "Day 15"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day15
