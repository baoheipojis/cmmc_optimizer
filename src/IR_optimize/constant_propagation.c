//
// Created by hby on 22-12-4.
//

#include <constant_propagation.h>


static CPValue meetValue(CPValue v1, CPValue v2) {
//   如果其中一个是UNDEF，那么结果就是另一个
    if(v1.kind == UNDEF) return v2;
    if (v2.kind == UNDEF) return v1;
    // 只要有一个是NAC, 结果就是NAC
    if(v1.kind == NAC || v2.kind == NAC) return get_NAC();
    // 如果两个都是常量，那么它们相等的话，就是这个常量，不等就是NAC
    if(v1.const_val == v2.const_val) return v1;
    return get_NAC();
}

static CPValue calculateValue(IR_OP_TYPE IR_op_type, CPValue v1, CPValue v2) {
    // 这里对应了软分实验中的evaluate。
    // 首先处理几个特殊情况：
    // 除0肯定是UNDEF
    if (v2.kind == CONST && v2.const_val == 0 && (IR_op_type == IR_OP_DIV))
      return get_UNDEF();
    // 如果其中一个是NAC，那么结果就是NAC
    if (v1.kind == NAC || v2.kind == NAC) {
      return get_NAC();
    }
    // 如果其中一个是UNDEF，那么结果就是UNDEF
    if(v1.kind == UNDEF || v2.kind == UNDEF) return get_UNDEF();
    // 下面只剩下两个都是CONST的情况了
    int res_const;
    switch (IR_op_type) {
        case IR_OP_ADD: res_const = v1.const_val + v2.const_val; break;
        case IR_OP_SUB: res_const = v1.const_val - v2.const_val; break;
        case IR_OP_MUL: res_const = v1.const_val * v2.const_val; break;
        case IR_OP_DIV:
            if(v2.const_val == 0) return get_UNDEF();
            res_const = v1.const_val / v2.const_val;
            break;
        default: return get_NAC(); // or assert(0);
    }
    return get_CONST(res_const);
}

// UNDEF等价为在Map中不存在该Var的映射项

static CPValue
Fact_get_value_from_IR_var(Map_IR_var_CPValue *fact, IR_var var) {
    return VCALL(*fact, exist, var) ? VCALL(*fact, get, var) : get_UNDEF();
}

static CPValue
Fact_get_value_from_IR_val(Map_IR_var_CPValue *fact, IR_val val) {
    if(val.is_const) return get_CONST(val.const_val);
    else return Fact_get_value_from_IR_var(fact, val.var);
}

static void
Fact_update_value(Map_IR_var_CPValue *fact, IR_var var, CPValue val) {
    if (val.kind == UNDEF) VCALL(*fact, delete, var);
    else VCALL(*fact, set, var, val);
}

static bool
Fact_meet_value(Map_IR_var_CPValue *fact, IR_var var, CPValue val) {
    CPValue old_val = Fact_get_value_from_IR_var(fact, var);
    CPValue new_val = meetValue(old_val, val);
    if(old_val.kind == new_val.kind && old_val.const_val == new_val.const_val)
        return false;
    Fact_update_value(fact, var, new_val);
    return true;
}


//// ============================ Dataflow Analysis ============================

static void ConstantPropagation_teardown(ConstantPropagation *t) {
    for_map(IR_block_ptr, Map_ptr_IR_var_CPValue, i, t->mapInFact)
        RDELETE(Map_IR_var_CPValue, i->val);
    for_map(IR_block_ptr, Map_ptr_IR_var_CPValue, i, t->mapOutFact)
        RDELETE(Map_IR_var_CPValue, i->val);
    Map_IR_block_ptr_Map_ptr_IR_var_CPValue_teardown(&t->mapInFact);
    Map_IR_block_ptr_Map_ptr_IR_var_CPValue_teardown(&t->mapOutFact);
}

static bool
ConstantPropagation_isForward (ConstantPropagation *t) {
    return true;
}

static Map_IR_var_CPValue*
ConstantPropagation_newBoundaryFact (ConstantPropagation *t, IR_function *func) {
    Map_IR_var_CPValue *fact = NEW(Map_IR_var_CPValue);
    for_vec(IR_var, param_ptr, func->params)
        // 初始化为NAC，这是显然的。因为如果变成Undef，那么Undef meet C = C，显然不合理
        VCALL(*fact, set, *param_ptr, get_NAC());
    return fact;
}

static Map_IR_var_CPValue*
ConstantPropagation_newInitialFact (ConstantPropagation *t) {
    return NEW(Map_IR_var_CPValue);
}

static void
ConstantPropagation_setInFact (ConstantPropagation *t,
                               IR_block *blk,
                               Map_IR_var_CPValue *fact) {
    VCALL(t->mapInFact, set, blk, fact);
}

static void
ConstantPropagation_setOutFact (ConstantPropagation *t,
                            IR_block *blk,
                            Map_IR_var_CPValue *fact) {
    VCALL(t->mapOutFact, set, blk, fact);
}

static Map_IR_var_CPValue*
ConstantPropagation_getInFact (ConstantPropagation *t, IR_block *blk) {
    return VCALL(t->mapInFact, get, blk);
}

static Map_IR_var_CPValue*
ConstantPropagation_getOutFact (ConstantPropagation *t, IR_block *blk) {
    return VCALL(t->mapOutFact, get, blk);
}

static bool
ConstantPropagation_meetInto (ConstantPropagation *t,
                              Map_IR_var_CPValue *fact,
                              Map_IR_var_CPValue *target) {
    bool updated = false;
    for_map(IR_var, CPValue, i, *fact)
        updated |= Fact_meet_value(target, i->key, i->val);
    return updated;
}

void ConstantPropagation_transferStmt (ConstantPropagation *t,
                                       IR_stmt *stmt,
                                       Map_IR_var_CPValue *fact) {
    if(stmt->stmt_type == IR_ASSIGN_STMT) {
        IR_assign_stmt *assign_stmt = (IR_assign_stmt*)stmt;
        IR_var def = assign_stmt->rd;
        CPValue use_val = Fact_get_value_from_IR_val(fact, assign_stmt->rs);
        // 如果是赋值语句，那么直接更新def的值就好了。
        Fact_update_value(fact, def, use_val);
    } else if(stmt->stmt_type == IR_OP_STMT) {
        IR_op_stmt *op_stmt = (IR_op_stmt*)stmt;
        IR_var def = op_stmt->rd;
        CPValue rs1_val = Fact_get_value_from_IR_val(fact, op_stmt->rs1);
        CPValue rs2_val = Fact_get_value_from_IR_val(fact, op_stmt->rs2);
        // 上面的rs表示操作数。这里就是计算操作数的值，然后更新def的值。
        CPValue new_val = calculateValue(op_stmt->op, rs1_val, rs2_val);
        Fact_update_value(fact, def, new_val);
    } else { // Other Stmt with new_def
        IR_var def = VCALL(*stmt, get_def);
        if(def != IR_VAR_NONE) {
            Fact_update_value(fact, def, get_NAC());
        }
    }
}

bool ConstantPropagation_transferBlock (ConstantPropagation *t,
                                        IR_block *block,
                                        Map_IR_var_CPValue *in_fact,
                                        Map_IR_var_CPValue *out_fact) {
    Map_IR_var_CPValue *new_out_fact = ConstantPropagation_newInitialFact(t);
    ConstantPropagation_meetInto(t, in_fact, new_out_fact);
    for_list(IR_stmt_ptr, i, block->stmts) {
        IR_stmt *stmt = i->val;
        ConstantPropagation_transferStmt(t, stmt, new_out_fact);
    }
    bool updated = ConstantPropagation_meetInto(t, new_out_fact, out_fact);
    RDELETE(Map_IR_var_CPValue, new_out_fact);
    return updated;
}

void ConstantPropagation_print_result (ConstantPropagation *t, IR_function *func) {
    printf("Function %s: Constant Propagation Result\n", func->func_name);
    for_list(IR_block_ptr, i, func->blocks) {
        IR_block *blk = i->val;
        printf("=================\n");
        printf("{Block%s %p}\n", blk == func->entry ? "(Entry)" :
                                 blk == func->exit ? "(Exit)" : "",
               blk);
        IR_block_print(blk, stdout);
        Map_IR_var_CPValue *in_fact = VCALL(*t, getInFact, blk),
                *out_fact = VCALL(*t, getOutFact, blk);
        printf("[In]:  ");
        for_map(IR_var, CPValue , j, *in_fact) {
            printf("{v%u: ", j->key);
            if(j->val.kind == NAC)printf("NAC} ");
            else printf("#%d} ", j->val.const_val);
        }
        printf("\n");
        printf("[Out]: ");
        for_map(IR_var, CPValue , j, *out_fact) {
            printf("{v%u: ", j->key);
            if(j->val.kind == NAC)printf("NAC} ");
            else printf("#%d} ", j->val.const_val);
        }
        printf("\n");
        printf("=================\n");
    }
}

void ConstantPropagation_init(ConstantPropagation *t) {
    const static struct ConstantPropagation_virtualTable vTable = {
            .teardown        = ConstantPropagation_teardown,
            .isForward       = ConstantPropagation_isForward,
            .newBoundaryFact = ConstantPropagation_newBoundaryFact,
            .newInitialFact  = ConstantPropagation_newInitialFact,
            .setInFact       = ConstantPropagation_setInFact,
            .setOutFact      = ConstantPropagation_setOutFact,
            .getInFact       = ConstantPropagation_getInFact,
            .getOutFact      = ConstantPropagation_getOutFact,
            .meetInto        = ConstantPropagation_meetInto,
            .transferBlock   = ConstantPropagation_transferBlock,
            .printResult     = ConstantPropagation_print_result
    };
    t->vTable = &vTable;
    Map_IR_block_ptr_Map_ptr_IR_var_CPValue_init(&t->mapInFact);
    Map_IR_block_ptr_Map_ptr_IR_var_CPValue_init(&t->mapOutFact);
}

//// ============================ Optimize ============================

// 常量折叠, 将所有use替换为相应常量
static void block_constant_folding (ConstantPropagation *t, IR_block *blk) {
    Map_IR_var_CPValue *blk_in_fact = VCALL(*t, getInFact, blk);
    Map_IR_var_CPValue *new_in_fact = ConstantPropagation_newInitialFact(t);
    ConstantPropagation_meetInto(t, blk_in_fact, new_in_fact);
    for_list(IR_stmt_ptr, i, blk->stmts) {
        IR_stmt *stmt = i->val;
        IR_use use = VCALL(*stmt, get_use_vec);
        for(int j = 0; j < use.use_cnt; j++)
            if(!use.use_vec[j].is_const) {
                IR_var use_var = use.use_vec[j].var;
                CPValue use_CPVal = Fact_get_value_from_IR_var(new_in_fact, use_var);
                if(use_CPVal.kind == CONST)
                    use.use_vec[j] = (IR_val){.is_const = true, .const_val = use_CPVal.const_val};
            }
        ConstantPropagation_transferStmt(t, stmt, new_in_fact);
    }
    RDELETE(Map_IR_var_CPValue, new_in_fact);
}

void ConstantPropagation_constant_folding (ConstantPropagation *t, IR_function *func) {
    for_list(IR_block_ptr, j, func->blocks) {
        IR_block *blk = j->val;
        block_constant_folding(t, blk);
    }
}


