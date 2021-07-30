#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.  

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
		 
		 
var_ordering == a function with the following template
    var_ordering(csp)
        ==> returns Variable 
        murdjmverefebchi

    csp is a CSP object---the heuristic can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    var_ordering returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

#= ----------------------------------------------------------------------------------
#=                                 Helper Functions
#= ----------------------------------------------------------------------------------

def FC_check(constraint, unAssignedVar, pruned):
    
    for dom in unAssignedVar.cur_domain():
        # Assign
        unAssignedVar.assign(dom)
        
        values = []
        for variable in constraint.get_scope():
            
            values.append(variable.get_assigned_value())
        
        # If does not satisfied
        if not constraint.check(values):
            pruned.append((unAssignedVar.prune_value(dom), dom))
        
        # UnAssign
        unAssignedVar.unassign()
    
    # DWO does not occurred: True 
    if unAssignedVar.cur_domain_size() != 0: return True
    # DWO occurred: False
    else: return False

#= ----------------------------------------------------------------------------------
def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''
    #IMPLEMENT
    
    # Get list of constraints
    if newVar != None: constraints = csp.get_cons_with_var(newVar)
    else: constraints = csp.get_all_cons()
    
    pruned = []
    for constraint in constraints:
        
        if constraint.get_n_unasgn() == 1:
            
            if not FC_check(constraint, constraint.get_unasgn_vars()[0], pruned):
                
                return False, pruned
    
    return True, pruned
    
    
def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    #IMPLEMENT
    
    pruned = []
    # Get list of constraints
    if newVar != None: 
        
        constraints = csp.get_cons_with_var(newVar)
        
        for value in newVar.cur_domain():
            
            if value != newVar.get_assigned_value():
                
                newVar.prune_value(value)
                pruned.append((newVar, value))
    
    else: constraints = csp.get_all_cons()
    
    while len(constraints) > 0:
        
        # Get the constraint at index 0
        constraint = constraints.pop(0)
        
        # Get all variables associated with this constrain
        variables = constraint.get_scope()
        
        for variable in variables :
            
            # Get domain
            curr_domain = variable.cur_domain()
            
            for value in curr_domain:
                
                if not constraint.has_support(variable, value):
                    
                    if variable.in_cur_domain(value):
                        
                        variable.prune_value(value)
                        pruned.append((variable, value))
                        
                        # DWO occurred
                        if variable.cur_domain_size() == 0:
                            return False, pruned
                        
                        # DWO does not occurred 
                        else:
                            
                            constraints2 = csp.get_cons_with_var(variable)
                            
                            for constraint2 in constraints2:
                                
                                if constraint2 not in constraints:
                                    
                                    constraints.append(constraint2)
               
                
    return True, pruned
    

def ord_mrv(csp):
    ''' return variable according to the Minimum Remaining Values heuristic '''
    #IMPLEMENT
    variables = csp.get_all_unasgn_vars()
    
    if len(variables) == 0: return None
    
    index = float("inf")
    
    for variable in variables:
        
        if variable.cur_domain_size() < index:
            
            index = variable.cur_domain_size()
            mrv = variable
    
    return mrv

	