import «Aoc2024».Util.GridArray
import «Aoc2024».Util.WeightedGraph 

namespace Day16

structure Maze (m n : Nat) where
  grid : GridArray m n Bool
  startTile : Idx m n
  endTile : Idx m n
  
namespace Maze

def ofLines (lines : Array String) : Except String ((m : Nat) × (n : Nat) × Maze m n) := do
  let lines := lines.map (·.toList.toArray)
  let ⟨m, n, grid⟩ ← GridArray.ofLines lines
  let startTile ← (GridArray.indices m n).filter (grid.get · = 'S')
    |>.head?
    |>.elim (Except.error "did not find start tile of Maze") Except.ok 
  let endTile ← (GridArray.indices m n).filter (grid.get · = 'E')
    |>.head?
    |>.elim (Except.error "did not find start tile of Maze") Except.ok 
  return ⟨m, n, { grid := grid.map (· != '#'), startTile, endTile }⟩

abbrev State (m n : Nat) := Idx m n × Direction

def graph (maze : Maze m n) : WeightedGraph (State m n) Nat where
  edges := fun (p, d) => ((p, d.cw), 1000) :: ((p, d.ccw), 1000) :: Option.toList do
    let p' ← p.move d
    let () ← guard <| maze.grid.get p
    return ((p', d), 1)
    
def bestPath (maze : Maze m n) : Option Nat :=
  let graph := maze.graph
  let bestPaths := graph.dijkstra (maze.startTile, Direction.R)
  Direction.univ.filterMap (fun d => bestPaths.get? (maze.endTile, d)) |>.min?

def bestPathCellCount (maze : Maze m n) : Option Nat := do
  let graph := maze.graph
  let bestStart := graph.dijkstra (maze.startTile, Direction.R)
  let bestPath ← Direction.univ.filterMap (fun d => bestStart.get? (maze.endTile, d)) |>.min?
  let bestDirections := Direction.univ.filter fun d => bestStart.get? (maze.endTile, d) = some bestPath
  -- have to do d.cw.cw because the movement is backwards
  let bestEnds := bestDirections.map fun d => graph.dijkstra (maze.endTile, d.cw.cw)
  return List.length <| GridArray.indices m n
    |>.filter (maze.grid.get ·)
    |>.filter fun p => Direction.univ.any fun d => some bestPath = do
      let x ← bestStart.get? (p, d)
      -- have to do d.cw.cw because the movement is backwards
      let y ← bestEnds.filterMap (·.get? (p, d.cw.cw)) |>.min?
      return x + y

end Maze

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day16/test.txt")
  let ⟨_, _, maze⟩ ← IO.ofExcept (Maze.ofLines lines)
  println! "Test: {maze.bestPath}"
  println! "Expected: {some 7036}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day16/task.txt")
  let ⟨_, _, maze⟩ ← IO.ofExcept (Maze.ofLines lines)
  println! "Task: {maze.bestPath}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day16/test.txt")
  let ⟨_, _, maze⟩ ← IO.ofExcept (Maze.ofLines lines)
  println! "Test: {maze.bestPathCellCount}"
  println! "Expected: {some 45}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day16/task.txt")
  let ⟨_, _, maze⟩ ← IO.ofExcept (Maze.ofLines lines)
  println! "Task: {maze.bestPathCellCount}"

end Task2

def main : IO Unit := do
  println! "Day 16"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day16
