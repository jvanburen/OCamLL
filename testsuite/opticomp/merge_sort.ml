open Array
       
let rec merge_sort arr =
  let len = length arr in
  if len < 2 then arr else
    let mid = len / 2 in
    let (arrA, arrB) = (merge_sort (sub arr 0 mid),
                        merge_sort (sub arr mid (len - mid))) in
    let aIdx = ref 0 in
    let bIdx = ref 0 in
    for i = 0 to len - 1 do
      if (!aIdx) = mid then set arr i (get arrB (!bIdx))
      else if !bIdx = len then set arr i (get arrA (!aIdx))
      else if !aIdx > !bIdx then set arr i (get arrB (!bIdx))
      else set arr i (get arrA (!aIdx))
    done;
    arr
      
let size = 1000000
let arr = make size 0
let _ = for i = 0 to size - 1 do
          set arr i (size - i)
        done
let _ = merge_sort arr
