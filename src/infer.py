# from check import Context, Definition, normalize
# from parse import AppTerm, ConstTerm, LambdaTerm, PiTerm, SortTerm, StarTerm, Term, VarTerm
# from subst import subst, subst_all


# class InferenceError(Exception):
#     pass


# def fmtErr_(t: Term, msg: str) -> InferenceError:
#     return InferenceError(f"{msg}")


# def infer(t: Term, env: list[Definition], ctx: Context) -> Term:
#     if isinstance(t, StarTerm):
#         return SortTerm()
#     elif isinstance(t, SortTerm):
#         raise fmtErr_(t, "sort cannot be typed")
#     elif isinstance(t, VarTerm):
#         mb_type = ctx.get(t.name)
#         if not mb_type:
#             raise fmtErr_(t, "variole not binded in context")
#         else:
#             return mb_type
#     elif isinstance(t,AppTerm):
#         op_type = infer(t.t1, env, ctx)
#         if not isinstance(op_type, PiTerm):
#             raise fmtErr_(t, "operand of app must have Pi type")
#         else:
#             return normalize(subst(op_type.t2, t.t2,op_type.name), env)
#     elif isinstance(t, ConstTerm):
#         mb_dfn = next((dfn for dfn in env if dfn.op == t.op), None)
#         if not mb_dfn:
#             raise fmtErr_(t, "definition not found")
#         else:
#             return normalize(subst_all(mb_dfn.body, mb_dfn.context.params(), t.children), env)
#     elif isinstance(t, LambdaTerm):
#         tp = infer(t.t2, env, ctx.extend(t.name, t.t1))
#         return normalize(tp, env)
#     elif isinstance(t, PiTerm):
#         tp = infer(t.t2, env, ctx.extend(t.name, t.t1))
#         if not (isinstance(tp, StarTerm) or isinstance(tp, SortTerm)):
#             raise fmtErr_(t, "Pi term must typed as some kind")
#         else:
#             return tp
#     else:
#         raise fmtErr_(t, "internal failure: pattern does not exhaustive")
