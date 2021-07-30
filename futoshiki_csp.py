#Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects 
representing the board. The returned list of lists is used to access the 
solution. 

For example, after these three lines of code

    csp, var_array = futoshiki_csp_model_1(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the Futoshiki puzzle.

1. futoshiki_csp_model_1 (worth 20/100 marks)
    - A model of a Futoshiki grid built using only 
      binary not-equal constraints for both the row and column constraints.

2. futoshiki_csp_model_2 (worth 20/100 marks)
    - A model of a Futoshiki grid built using only n-ary 
      all-different constraints for both the row and column constraints. 

'''
from cspbase import *
import itertools


#= ----------------------------------------------------------------------------------
#=                                 Helper Functions
#= ----------------------------------------------------------------------------------

def check(ineq, var_1, var_2, val_1, val_2):

    if var_1[1] + 1 == var_2[1]: return val_1 != val_2 and check_ineq(ineq, val_1, val_2)

    else: return val_1 != val_2

def check_ineq(ineq, val_1, val_2):
    
    if ineq == '>': return val_1 > val_2
    
    elif ineq == '<': return val_1 < val_2
    
    else: return True

def get_var_and_ineq(futo_grid, vars_all, dom, row_num, col_num, var_array, ineq_array):
    
    for i in range(0, row_num):
        
        row_var, row_ineq = [], []
        for j in range(0, col_num):
            
            if j % 2 == 0:
                
                if futo_grid[i][j] == 0: var_temp = Variable("V{}{}".format(i, j // 2), dom)
                
                else: var_temp = Variable("V{}{}".format(i, j // 2), [futo_grid[i][j]])

                row_var.append(var_temp)
                vars_all.append(var_temp)

            else:
                row_ineq.append(futo_grid[i][j])

        var_array.append(row_var)
        ineq_array.append(row_ineq)

def check_nary(vars, vals):
    
    for i in range(len(vars)):
        
        for j in range(i+1, len(vars)):
            
            if vals[i] == vals[j]: return False

    return True

def make_sat_tuple_1(dom_1, dom_2, i, j, k, ineq_array, c):
    sat_tup = []  
    for sat in itertools.product(dom_1, dom_2):
        
        if check(ineq_array[i][j], (i, j), (i, k), sat[0], sat[1]): sat_tup.append(sat)
        
    c.add_satisfying_tuples(sat_tup)
    
    return c

def make_sat_tuple_2(dom_1, dom_2, i, j, k, c):
    sat_tup = []
    for sat in itertools.product(dom_1, dom_2):
        
        if check('.', (j, i), (k, i), sat[0], sat[1]): sat_tup.append(sat)
            
    c.add_satisfying_tuples(sat_tup)
    
    return c

def make_sat_tuple_3(dom_1, dom_2, i, j, ineq_array, c):
    sat_tup = []
    for sat in itertools.product(dom_1 , dom_2):
        
        if check_ineq(ineq_array[i][j], sat[0], sat[1]): sat_tup.append(sat)
    
    c.add_satisfying_tuples(sat_tup)
    
    return c

def make_sat_tuple_4(rowOrCol_vars, vars_rowOrCol_dom, c):
    sat_tup = []
    for sat in itertools.product(*vars_rowOrCol_dom):
        
        if check_nary(rowOrCol_vars, sat): sat_tup.append(sat)
            
    c.add_satisfying_tuples(sat_tup)
    
    return c

def check_adj_1(constraints, var_array, ineq_array):
    
    for i in range(0, len(var_array)):
        
        for j in range(0, len(var_array)):
            
            for k in range(j+1, len(var_array)):
                
                var_1, var_2 = var_array[i][j], var_array[i][k]
                constraints.append(
                    make_sat_tuple_1(var_1.cur_domain(), 
                                     var_2.cur_domain(), 
                                     i,
                                     j, 
                                     k, 
                                     ineq_array, 
                                     Constraint("Constraint(V{}{}, V{}{})".format(i, j, i, k), 
                                                [var_1, var_2])))

                var_1, var_2 = var_array[j][i],  var_array[k][i]        
                constraints.append(
                    make_sat_tuple_2(var_1.cur_domain(), 
                                     var_2.cur_domain(), 
                                     i, 
                                     j, 
                                     k, 
                                     Constraint("Constraint(V{}{}, V{}{})".format(j, i, k, i), 
                                                [var_1, var_2])) )

def check_adj_2(constraints, var_array, ineq_array):
    
    for i in range(0, len(var_array)):
        
        row_vars, col_vars = var_array[i], []
        vars_row_dom ,vars_col_dom = [], [] 
        for j in range(0, len(var_array)):
            
            col_vars.append(var_array[j][i])
            vars_row_dom.append(var_array[i][j].cur_domain())
            vars_col_dom.append(var_array[j][i].cur_domain())
            
            if j < len(ineq_array[i]):
                
                var_1, var_2 = var_array[i][j], var_array[i][j+1]
                if ineq_array[i][j] != '.':
                
                    constraints.append(
                        make_sat_tuple_3(var_1.cur_domain(), 
                                         var_2.cur_domain(), 
                                         i, 
                                         j, 
                                         ineq_array, 
                                         Constraint("Constraint(V{}{}, V{}{})".format(i, j, i, j + 1), 
                                                    [var_1, var_2])))

        constraints.append(make_sat_tuple_4(row_vars, 
                                            vars_row_dom, 
                                            Constraint("Constraints(R{})".format(i), 
                                                       row_vars)))
        
        constraints.append(make_sat_tuple_4(col_vars, 
                                            vars_col_dom, 
                                            Constraint("Constraints(R{})".format(i), 
                                                       col_vars)))


#= ----------------------------------------------------------------------------------

def futoshiki_csp_model_1(futo_grid):
    ##IMPLEMENT
      
    constraints, vars_all, var_array, ineq_array = [], [], [], []
    
    row_num, col_num = len(futo_grid), len(futo_grid[0])

    dom = [i + 1 for i in range(row_num)]

    get_var_and_ineq(futo_grid, vars_all, dom, row_num, col_num, var_array, ineq_array)

    check_adj_1(constraints, var_array, ineq_array)

    cspObject = CSP("Solver_1 with size {}".format(len(var_array)), vars_all)
    
    for c in constraints: 
        cspObject.add_constraint(c)

    return cspObject, var_array
    

def futoshiki_csp_model_2(futo_grid):
    ##IMPLEMENT 
    
    constraints, vars_all, var_array, ineq_array = [], [], [], []

    row_num, col_num = len(futo_grid), len(futo_grid[0])

    dom = [i + 1 for i in range(row_num)]

    get_var_and_ineq(futo_grid, vars_all, dom, row_num, col_num, var_array, ineq_array)

    check_adj_2(constraints, var_array, ineq_array)

    cspObject = CSP("Solver_2 with size {}".format(len(var_array)), vars_all)
    
    for c in constraints:
        cspObject.add_constraint(c)

    return cspObject, var_array

   
