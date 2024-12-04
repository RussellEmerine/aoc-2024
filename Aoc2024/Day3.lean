namespace Day3

namespace Task1

def task1 (s : String) : Nat := Id.run <| do
  let mut sum := 0
  for i in List.range s.length do
    if "mul(" != ((s.toSubstring.drop i).take 4).toString then 
      continue 
    for p in [1, 2, 3] do
      for q in [1, 2, 3] do
        if "," != ((s.toSubstring.drop (i + 4 + p)).take 1).toString then 
          continue 
        if ")" != ((s.toSubstring.drop (i + 4 + p + 1 + q)).take 1).toString then 
          continue
        let a := ((s.toSubstring.drop (i + 4)).take p).toString
        let b := ((s.toSubstring.drop (i + 4 + p + 1)).take q).toString
        if let (some x, some y) ← (a.toNat?, b.toNat?) then do
          sum := sum + x * y
  return sum 

def main : IO Unit := do
  let test ← IO.FS.readFile (System.FilePath.mk "Data/Day3/test.txt")
  println! "Test: {task1 test}"
  println! "Expected: {161}"
  let task ← IO.FS.readFile (System.FilePath.mk "Data/Day3/task.txt")
  println! "Task: {task1 task}"

end Task1

namespace Task2

def task2 (s : String) : Nat := Id.run <| do
  let mut sum := 0
  let mut enabled := true
  for i in List.range s.length do
    if "do()" = ((s.toSubstring.drop i).take 4).toString then 
      enabled := true
    if "don't()" = ((s.toSubstring.drop i).take 7).toString then 
      enabled := false
    if "mul(" != ((s.toSubstring.drop i).take 4).toString then 
      continue 
    for p in [1, 2, 3] do
      for q in [1, 2, 3] do
        if "," != ((s.toSubstring.drop (i + 4 + p)).take 1).toString then 
          continue 
        if ")" != ((s.toSubstring.drop (i + 4 + p + 1 + q)).take 1).toString then 
          continue
        let a := ((s.toSubstring.drop (i + 4)).take p).toString
        let b := ((s.toSubstring.drop (i + 4 + p + 1)).take q).toString
        if let (some x, some y) ← (a.toNat?, b.toNat?) then do
          if enabled then do
            sum := sum + x * y
  return sum 

def main : IO Unit := do
  let test ← IO.FS.readFile (System.FilePath.mk "Data/Day3/test.txt")
  println! "Test: {task2 test}"
  println! "Expected: {48}"
  let task ← IO.FS.readFile (System.FilePath.mk "Data/Day3/task.txt")
  println! "Task: {task2 task}"

end Task2

def main : IO Unit := do
  println! "Day 3"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day3
