# Debugging simplification by cbv

If symbols are missing in the delta list, the resulting terms can become very large and it can take minutes to run cbv.

## Using Coqtop and batch debug

Usually coqtop is faster in displaying terms than most IDEs - also it obeys `Set Printing Depth`.

To use coqtop try the following:

- put your current file until including the failing tactic call into a file `Debug.v`
- put the following commands in front of the failing tactic:
    ``` 
    Set Printing Depth 1000.
    Set Printing Width 240.
    Unset Printing Notations.
    Set Printing Implicit.
    Set Ltac Debug.
    Set Ltac Batch Debug.
    ```
- put a `Quit.` after the failing tactic.
- run `coqtop <required -Q flags> -lv Debug.v 2>&1 | ts -i "%.s" 1>Debug.log`
- the `ts` command adds run times in us at the begin of each line - you can search the log for longer times with a regexp
  - if you don't want the time stamps, remove this from the pipe
- look into `Debug.log` and find the long running command
- assuming you waited long enough for it to finish, you will find teh resulting goal after it
- In this goal typically you have a longish half expanded function application, which is applied to a term containing variables
- Jump after the function term using "go to matched parenthesis" and see what it is applied on - this term is usually not that long and one can find out by inspection why it does not compute.
- The `Debug.log` can be long (a few 10 million lines is not unheard of) - if you have issues with modern editors, use vi
  - search forward / backward is `/` and `?``
  - search matching parenthesis is `%`