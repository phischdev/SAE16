

//------------------Project 1-------------------------------------
//---------------------------------------------------------------
//------------Philipp Schimmelfennig -Panuya Balasuntharam------------
//---------------------------------------------------------------

abstract sig LinearProgram{
	function: some Function,
	mainFunction: one MainFunction
}


--------------------------Type-------------------------------------

sig Type {
	superType: lone Type
}


sig Function {
	returnType: one Type, 
	formalParameter: set FormalParameter,
	belongsToOneLinPr: one LinearProgram, 
	sequence: one  LinearSequenceOfStatement
}

sig MainFunction extends Function{}


fact belongsToFunction{
	all f: Function | all l:LinearProgram | f.belongsToOneLinPr = l <=> l.function = f
}


fact mainFunctionHasNoParameter{
	all m: MainFunction | m.formalParameter = none
}

fact mainFunctionBelongsToAFunction{
	all m: MainFunction | all p: LinearProgram | p.mainFunction = m <=> m.belongsToOneLinPr = p
}

/*

fact avoidRecursion{
	
}
*/
-------------------------Parameter--------------------------------

abstract sig Parameter {
	type: one Type
}

sig FormalParameter extends Parameter {
	belongsTo: one Function,
	belongsToOneVariable: one Variable
}

sig ActualParameter extends Parameter {
	expression: one Expr
}


fact reflexitivFormalParameter{
	all f: Function | all p: FormalParameter | f.formalParameter = p <=> p.belongsTo = f
}


--------------------------Statement-----------------------------

sig LinearSequenceOfStatement {
	belongsTo: one Function,
	firstStatement: one Statement,
	lastStatement: one ReturnStatement,
	statements: some Statement
}

abstract sig Statement {
	nextStatement: lone Statement,
	expression: lone Expr
}

sig AssignementStatement  extends Statement{
	variable: one DeclaredVariable,
	expressions: one Expr
}

sig ReturnStatement extends Statement{
	isIn: one LinearSequenceOfStatement
}



fact ReturnStatementLinearSequence {
	all r: ReturnStatement | all s: LinearSequenceOfStatement | r.isIn = s <=> s.lastStatement = r
}


fact sequenceBelongsToFunction{
	all f: Function | all s: LinearSequenceOfStatement   | f.sequence = s <=> s.belongsTo = f
}



fact allStatementMustAppear{
	(all a: AssignementStatement |all s: LinearSequenceOfStatement  |a in s.statements) && (all d: VarDecl |all s: LinearSequenceOfStatement  |d in s.statements)
}

fact noCircle{
	all s1, s2: Statement | s1.nextStatement = s2 => s1 not in s2.^nextStatement
}

fact expressionMustAppearInStatement {
	all e: Expr | all s: Statement | e in s.expression
}


fact lastStatementReturnstatement{
	all r: ReturnStatement | r.nextStatement = none
}


fact statement{
 all s: LinearSequenceOfStatement |all x: Statement | x in s.statements <=> x in (s.firstStatement.^nextStatement + s.firstStatement)
} 

fact ReturnStatement {
	all r: ReturnStatement | all s: LinearSequenceOfStatement | r in s.statements
}


fact noItSelf{
	all s:Statement | s.nextStatement != s
}

fact differentNextStatement {
	all s1, s2, s3: Statement | s1.nextStatement = s2 => s3.nextStatement != s2
}


------------------------------------------------------------------

sig Expr {
	type: one Type,
	consistsOf: set Expr
}

sig Literal extends Expr {}

sig CallExpression extends Expr {
	calledFunction: one Function,
	actualParameter: set ActualParameter
}

fact canNotConsistItself{
	all e: Expr | e not in e.consistsOf
}

---------------------------Expression Tree-----------------------
sig Node {
	parent: lone Node,
	children: set Node,
	exprTree: one ExpressionTree
}

sig ExpressionTree {
	root: one Node,
	leaves: set Node
}



fact parentChildrenRelationsship{
	all n1, n2: Node | n1. parent = n2  <=> n1 in n2.children 
}


// unsicher ob dies funktioniert. Ich möchte root definieren
fact root{
	(all r: ExpressionTree | all n: Node | r.root in n.^parent)&&
	(all r: ExpressionTree | all n: Node | r. root not in n.^children)
}

fact notSameRootAndLeaves{
	all e: ExpressionTree | e.root not in e.leaves
}

fact notOwnChild {
	all n: Node | n not in n.children
}

fact notOwnParent{
	all n: Node | n not in n.parent
}

fact notSameRoot{
	all e1, e2: ExpressionTree | e1.root != e2.root
}

fact parentAndChildHasTheSameExprTree {
	all n1, n2: Node | n1.parent = n2 => n1.exprTree = n2.exprTree
}



-------------------------------Variable-----------------------------------------
/*
sig Variable {
	declaredVariables: set DeclaredVariable,
	formalParameters: set FormalParameter, 
	assignedVariables: set AssignedVariable,
	belongsTo: one Function
}
*/

sig Variable {}


sig VariableReference extends Expr{
	fvariable: lone FormalParameter,
	avariable: lone AssignedVariable
}


sig DeclaredVariable extends Variable{
	type: one Type
}

sig AssignedVariable extends DeclaredVariable {
	readIn: some Expr
}


sig VarDecl extends Statement{
	type: one Type
} 

// in UML we call it DeclarationStatement


fact onlyOneVariableReference {
	all v: VariableReference | all f: FormalParameter | all a: AssignedVariable| (f in v.fvariable => a not in  v.avariable) && (a in  v.avariable => f not in v.fvariable)
}

/*

fact variablelist{
	(all d: DeclaredVariable | all v: Variable | d in v.declaredVariables <=> d.belongsTo = v) &&
	(all p: FormalParameter | all v: Variable | p in v.formalParameters  <=> p.belongsToOneVariable = v) 
}

*/






//----------------------Functions--------------------------------


fun p_numFunctionCalls[]:Int {
	#CallExpression
}


/*fun p_expressionTypes[]:set Type {

}*/


/*
fun p_literalTypes[]:set Type {}
*/


/*
fun p_parameters[f:Function]:set FormalParameter {

}

*/


-- Predicates --------------


pred p_ContainsCall [f: Function] {
  # {x: Expr | x in ( f.sequence.firstStatement.^nextStatement ).expression} > 0
}

/*
pred p_isAssigned [v: Variable] {
  some f: Function | some s:AssignementStatement | s in f.sequence.statements && s.variable = v
}

pred p_isRead [v: Variable] {
  some f: Function | some s:VariableReference | s in f.sequence.statements.expressions && s.variable = v
}


pred p_isDeclared [v: Variable] {
  some f: Function | some s:DeclarationStatemente | s in f.sequence.statements && s.variable = v


pred p_isSubtype [t1: Type, t2: Type] {
  t1 in t2.^superType
}

pred p_assignsTo [s: Statement, vd: VarDecl] {
  s.variable = vd.variable
}
*/

pred show {}

run show for 5
