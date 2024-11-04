/**
 * Identifies uses of __builtin_expect() in non-conditional contexts.
 * As of now a hypothetical use of
 * ```c
 * x = FD_UNLIKELY(...);
 * if (x) {...}
 * ```
 * will lead to a false positive.
 * The dataflow analysis needed to detect this has an unreasonable runtime
 * complexity, given that this is never done in FD.
 * @id cpp/builtin-expect-scope-too-narrow
 * @kind problem
 * @severity warning
 */

import cpp
import filter


from FunctionCall builtinCall, Element e
where
  builtinCall.getTarget().getName() = "__builtin_expect" and
  builtinCall.getParent() = e and
  not ((e instanceof ConditionalStmt) or
       (e instanceof Loop) or
       (e instanceof BinaryLogicalOperation) or
       (e instanceof ConditionalExpr)) and
  included(builtinCall.getLocation())
select builtinCall, "Use of __builtin_expect() in non-conditional context"