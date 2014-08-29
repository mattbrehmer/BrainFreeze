//source/BrainFreezeInclude

/** IMPORT STATEMENTS **/

import flash.events.Event;
import flash.events.MouseEvent;
import flash.events.OutputProgressEvent;
import flash.events.TimerEvent;
import flash.filesystem.File;
import flash.filesystem.FileMode;
import flash.filesystem.FileStream;
import flash.utils.Timer;
import flash.utils.getDefinitionByName;
import flash.utils.getQualifiedClassName;

import flashx.textLayout.formats.Float;

import graphics.IDraggableGraphic;

import interruptions.InterruptionHD;
import interruptions.InterruptionHigh;
import interruptions.InterruptionLow;
import interruptions.InterruptionPrompt;

import mx.collections.ArrayCollection;
import mx.controls.Alert;
import mx.core.IUIComponent;
import mx.core.IVisualElement;
import mx.core.UIComponent;
import mx.core.mx_internal;
import mx.events.DragEvent;
import mx.managers.DragManager;
import mx.managers.PopUpManager;

import puzzles.*;

import spark.components.TitleWindow;
import spark.filters.DropShadowFilter;
import spark.primitives.Graphic;

/** PRIVATE VARIABLES **/

//mouseDown X+Y offset for a draggable object 
private var offsetX:Number;
private var offsetY:Number;		

//x,y source coordinates of moved items
private var sourceX:Number;
private var sourceY:Number;		

//maintain depth variable to allow layering of items in SC
private var maxDepth:Number = 1;	

//vars for tracking number of items moved (valid, invalid, aborted) and clicked
private var elementsMoved:Number = 0;
private var moveAdjustments:Number = 0;
private var completedActions:Number = 0;
private var completedActionsSinceInterruption:Number = 0;
private var elementsClicked:Number = 0;
private var abortedMoves:Number = 0;
private var invalidMoves:Number = 0;

//the max number of puzzles (SC = 10, SqP = 8, 3 each in training sets)
private var MAX_SC_PUZZLE:Number;
private var MAX_SqP_PUZZLE:Number;

//puzzle instruction strings
[Bindable] private var sqp_instructionText:String; 
[Bindable] private var sc_instructionText:String; 

//interruption complexity flag/trial (0 = none, 1 = low, 2 = high)
private var interruptionType:Number = 0;

//main task flag: false = SC, true = SqP
private var mainTaskType:Boolean = false;

//false = SC first, true = SqP first
[Bindable]private var mainTaskOrder:Boolean = false;

//variables associated with inter-action intervals
private var firstAction:Boolean = false;
private var firstActionTime:Number = 0;
private var lastActionTime:Number = 0;
private var interruptionTime:Number = 0;
private var interActionTotal:Number = 0;
private var postInterruption:Boolean = false;
private var interActionIntervalBefore:Number = 0;
private var interActionIntervalAfter:Number = 0;

//interruptState data for comboBox
[Bindable]public var interruptState:ArrayCollection = new ArrayCollection(
	[	{label:"", first:0, second:0, third:0},
		{label:"NLH", first:0, second:1, third:2}, 
		{label:"NHL", first:0, second:2, third:1}, 
		{label:"LNH", first:1, second:0, third:2}, 
		{label:"LHN", first:1, second:2, third:0}, 
		{label:"HNL", first:2, second:0, third:1}, 
		{label:"HLN", first:2, second:1, third:0} 
	]);

//interruption sequence (NLH) for each task
private var scInterruptSeq:Array = new Array(3);
private var sqpInterruptSeq:Array = new Array(3);

//task order (ABC) for each main task
private var scTaskBankOrder:Array = new Array(3);
private var sqpTaskBankOrder:Array = new Array(3);

//trials on which interrupts occur within each task bank for SC and SqP
private var scInterruptTrialSubset:Array = new Array(4);
private var sqpInterruptTrialSubset:Array = new Array(3);

//interruption onset times for SC puzzles
public var scInterruptionOnsets:ArrayCollection = new ArrayCollection(
	[ 	{time:0}, //0: difficulty level: 1, required moves: 1
		{time:1000}, //1: difficulty level: 2, required moves: 1
		{time:1000}, //2: difficulty level: 2, required moves: 1
		{time:1000}, //3: difficulty level: 2, required moves: 1
		{time:1000}, //4: difficulty level: 1, required moves: many
		{time:2000}, //5: difficulty level: 3, required moves: 1
		{time:3000}, //6: difficulty level: 2, required moves: many
		{time:1000}, //7: difficulty level: 1, required moves: many
		{time:3000}, //8: difficulty level: 2, required moves: many
		{time:2000}  //9: difficulty level: 3, required moves: 3
	]);

//overall progress counters
private var globalCount:Number = 0;
private var scCount:Number = 0;
private var sqpCount:Number = 0;

private var scPracTask:SCPrac;
private var sqPPracTask:SqPPrac;

//time spent reading the SC instruction
private var scInstructionReadTimer:Timer = new Timer(1,0);

//time and event log files
private var SCTimeResults:File= File.documentsDirectory;	
private var SCTimeResultStream:FileStream = new FileStream();    	
private var SqPTimeResults:File= File.documentsDirectory;	
private var SqPTimeResultStream:FileStream = new FileStream();
private var taskResults:File = File.documentsDirectory;	
private var nBackResults:File = File.documentsDirectory;	

/** PUBLIC VARIABLES **/

//the current puzzle index
public var currentPuzzle:Number = -1;

//ID variables
public var groupID:String;
public var subjectID:String;

//interruption complexity flag/condition (0 = none, 1 = low, 2 = high)
public var interruptionCondition:Number = 0;

//time and event log files
public var taskResultStream:FileStream = new FileStream();
public var nBackResultStream:FileStream = new FileStream();

//time on task (TOT) timer
public var taskTimer:Timer = new Timer(1,0);

//task resumption lag (RLT) timer
public var resumptionTimer:Timer = new Timer(1,0);

//time to dismiss interruption
public var interruptionDismissalTime:int = 0;

//n-back performance
public var nBackScore:Number = 0;

/** I/O FUNCTIONS **/

//creates output files for logging time and task actions
private function initOutput():void
{
	//date and time stamp the log files
	var currentTime:Date = new Date();	
	
	trace("\n" + String(currentTime) + 
		": application started, log files created");
	
	//set group and subject ids
	groupID = groupIDNum.text;
	subjectID = subjectIDNum.text;
	
	if (groupID == "")
		groupID = "0";
	if (subjectID == "")
		subjectID = "0";
	
	var defaultFilename:String = 
		"g" + groupID +
		"s" + subjectID +
		"_[" + String(currentTime.getMonth() + 1) +
		"." + String(currentTime.getDate()) + 
		"_" + String(currentTime.getHours()) + 
		"." + String(currentTime.getMinutes()) + "]_";
	
	var defaultTimeHeader:String = 
		"gid\t" + //group id#
		"sid\t" + //subject id#
		"pid\t" + //puzzle id#
		"mvs\t" + //# valid moves
		"adj\t" + //# move adjustments (move within 50 pixels)
		"clks\t" + //# clicks
		"abrt\t" + //# aborted moves
		"ivld\t" + //# invalid moves
		"cmpx\t" + //interrupton complexity (0/none,1/unfilled,2/filled)
		"SCR\t\t" + //SC instruction reading time 
		"FCT\t\t" + //time until first click
		"nBK\t\t" + //n-back performance
		"IDT\t\t" + //time to dismiss interruption
		"RLT\t\t" + //resumption lag time
		"IAI1\t\t" + //inter-action interval (pre-interruption)
		"IAI2\t\t" + //inter-action interval (post-interruption)
		"TOT\t\t\t" + //total time on task
		"state"; // current puzzle set
	
	var nBackHeader:String = 
		"gid\t" + //group id#
		"sid\t" + //subject id#
		"pid\t" + //puzzle id#
		"tp\t" + //true positives
		"tn\t" + //true negatives
		"fp\t" + //false positives
		"fn\t" + //false negatives
		"cor\t" + //total correct
		"inc\t" + //total incorrect
		"state\n"; // current puzzle set
	
		
	//initialize SC time results output
	var SCTimeResultFilename:String = defaultFilename + "SCTimeResults.txt";
	SCTimeResults = taskResults.resolvePath(SCTimeResultFilename);
	SCTimeResultStream.open(SCTimeResults, FileMode.APPEND);	
	SCTimeResultStream.writeUTFBytes(defaultTimeHeader);
	
	//initialize SqP time results output
	var SqPTimeResultFilename:String = defaultFilename + "SqPTimeResults.txt";
	SqPTimeResults = taskResults.resolvePath(SqPTimeResultFilename);
	SqPTimeResultStream.open(SqPTimeResults, FileMode.APPEND);	
	SqPTimeResultStream.writeUTFBytes(defaultTimeHeader);
	
	//initialize task results output
	var taskResultFilename:String = defaultFilename + "taskResults.txt";
	taskResults = taskResults.resolvePath(taskResultFilename);
	taskResultStream.open(taskResults, FileMode.APPEND);	
	taskResultStream.writeUTFBytes(taskResultFilename);
	
	//initialize n-back task results output
	var nBackResultFilename:String = defaultFilename + "nBackResults.txt";
	nBackResults = nBackResults.resolvePath(nBackResultFilename);
	nBackResultStream.open(nBackResults, FileMode.APPEND);	
	nBackResultStream.writeUTFBytes(nBackHeader);
}

// randomize task bank (ABC) ordering and interruption trial subset
private function initRandomTask():void
{	
	// randomize task bank (ABC) ordering in SC
	var scTaskRand1:Number = Math.ceil(Math.random() * 3);
	var scTaskRand2:Number = Math.ceil(Math.random() * 2);
		
	var outputText:String = "\n### interruption sequence set: " +
		String(interruptStateCB.selectedItem.label);
	
	if (mainTaskOrder)
		outputText += "\n### main task order: SqP-SC";
	else
		outputText += "\n### main task order: SC-SqP";
	
	switch (scTaskRand1)
	{
		case 1:
			scTaskBankOrder[0] = "sc_a";
			if (scTaskRand2 == 2)
			{
				scTaskBankOrder[1] = "sc_b";
				scTaskBankOrder[2] = "sc_c";
			}
			else
			{
				scTaskBankOrder[1] = "sc_c";
				scTaskBankOrder[2] = "sc_b";
			}				
			break;
		case 2:
			scTaskBankOrder[0] = "sc_b";
			if (scTaskRand2 == 2)
			{
				scTaskBankOrder[1] = "sc_a";
				scTaskBankOrder[2] = "sc_c";
			}
			else
			{
				scTaskBankOrder[1] = "sc_c";
				scTaskBankOrder[2] = "sc_a";
			}				
			break;
		default:
			scTaskBankOrder[0] = "sc_c";
			if (scTaskRand2 == 2)
			{
				scTaskBankOrder[1] = "sc_a";
				scTaskBankOrder[2] = "sc_b";
			}
			else
			{
				scTaskBankOrder[1] = "sc_b";
				scTaskBankOrder[2] = "sc_a";
			}				
			break;			
	}
	
	outputText += "\n### tSC task order: " + scTaskBankOrder[0] + ", " + 
		scTaskBankOrder[1] + ", " + scTaskBankOrder[2];
			
	// randomize task bank (ABC) ordering in SqP
	var sqpTaskRand1:Number = Math.ceil(Math.random() * 3);
	var sqpTaskRand2:Number = Math.ceil(Math.random() * 2);
	
	switch (sqpTaskRand1)
	{
		case 1:
			sqpTaskBankOrder[0] = "sqp_a";
			if (sqpTaskRand2 == 2)
			{
				sqpTaskBankOrder[1] = "sqp_b";
				sqpTaskBankOrder[2] = "sqp_c";
			}
			else
			{
				sqpTaskBankOrder[1] = "sqp_c";
				sqpTaskBankOrder[2] = "sqp_b";
			}				
			break;
		case 2:
			sqpTaskBankOrder[0] = "sqp_b";
			if (sqpTaskRand2 == 2)
			{
				sqpTaskBankOrder[1] = "sqp_a";
				sqpTaskBankOrder[2] = "sqp_c";
			}
			else
			{
				sqpTaskBankOrder[1] = "sqp_c";
				sqpTaskBankOrder[2] = "sqp_a";
			}				
			break;
		default:
			sqpTaskBankOrder[0] = "sqp_c";
			if (sqpTaskRand2 == 2)
			{
				sqpTaskBankOrder[1] = "sqp_a";
				sqpTaskBankOrder[2] = "sqp_b";
			}
			else
			{
				sqpTaskBankOrder[1] = "sqp_b";
				sqpTaskBankOrder[2] = "sqp_a";
			}				
			break;			
	}
	
	outputText += "\n### tSqP task order: " + sqpTaskBankOrder[0] + ", " + 
		sqpTaskBankOrder[1] + ", " + sqpTaskBankOrder[2];
		
	// randomize interruption trial subset in SC
	var scInterruptRand1:Number = Math.ceil(Math.random() * 2);
	var scInterruptRand2a:Number = Math.ceil(Math.random() * 3);
	var scInterruptRand2b:Number = Math.ceil(Math.random() * 2);
	var scInterruptRand3:Number = Math.ceil(Math.random() * 2);
	
	if (scInterruptRand1 == 2) //level 1 difficulty interrupt on trial 4 or 7
		scInterruptTrialSubset[0] = 4;
	else
		scInterruptTrialSubset[0] = 7;
	if (scInterruptRand2a == 3)//level 2 difficulty interrupt on trials 1,2, or 3
		scInterruptTrialSubset[1] = 3;
	else if (scInterruptRand2a == 2)
		scInterruptTrialSubset[1] = 2;
	else
		scInterruptTrialSubset[1] = 1;
	if (scInterruptRand2b == 2)//level 2 difficulty interrupt on trials 6 or 8
		scInterruptTrialSubset[2] = 8;
	else
		scInterruptTrialSubset[2] = 6;
	if (scInterruptRand2b == 2)//level 3 difficulty interrupt on trials 5 or 9
		scInterruptTrialSubset[3] = 9;
	else
		scInterruptTrialSubset[3] = 5;
	
	outputText += "\n### SC interrupt subset: " + scInterruptTrialSubset[0] + ", " + 
		scInterruptTrialSubset[1] + ", " + scInterruptTrialSubset[2] + ", " + 
		scInterruptTrialSubset[3];
	
	var sqpInterruptRand2a:Number = Math.ceil(Math.random() * 2);
	var sqpInterruptRand2b:Number = Math.ceil(Math.random() * 2);
	var sqpInterruptRand3:Number = Math.ceil(Math.random() * 3);
	
	if (sqpInterruptRand2a == 2) //level 2 difficulty interrupt on trial 1 or 2
		sqpInterruptTrialSubset[0] = 2;
	else
		sqpInterruptTrialSubset[0] = 1;
	if (scInterruptRand2b == 2)//level 2 difficulty interrupt on trials 3 or 4
		sqpInterruptTrialSubset[1] = 4;	
	else
		sqpInterruptTrialSubset[1] = 3;
	if (sqpInterruptRand3 == 3)//level 3 difficulty interrupt on trials 5,6, or 7
		sqpInterruptTrialSubset[2] = 7;
	else if (sqpInterruptRand3 == 2)
		sqpInterruptTrialSubset[2] = 6;
	else
		sqpInterruptTrialSubset[2] = 5;
	
	outputText += "\n### SqP interrupt subset: " + sqpInterruptTrialSubset[0] + ", " + 
		sqpInterruptTrialSubset[1] + ", " + sqpInterruptTrialSubset[2];
	
	trace(outputText);
	taskResultStream.writeUTFBytes(outputText);	
}

//report current qualititative results
protected function taskResultOutputHandler():void
{
	//record # of items clicked and moved
	var taskResultsOutput:String = 
		"\n\n\t[" + String(taskTimer.currentCount * 10) + " ms]: " +
		"TASK COMPLETE; SUMMARY: " +
		"\n\t\telements clicked: " + 
			String(elementsClicked) + 
		"\n\t\telements moved: " + 
			String(elementsMoved) + 
		"\n\t\tmove adjustments: " + 
			String(moveAdjustments) + 
		"\n\t\taborted moves: " + 
			String(abortedMoves) + 
		"\n\t\tinvalid moves: " + 
			String(invalidMoves) + 
		"\n\t\tinstruction read time: " +
			"[" + String(scInstructionReadTimer.currentCount * 10) + " ms]" + 
		"\n\t\tfirst click time: " +
			"[" + String(firstActionTime) + " ms]" + 
		"\n\t\tinterruption dismissal lag: " +
			"[" + String(interruptionDismissalTime) + " ms]" +
		"\n\t\tresumption lag: " +
			"[" + String(resumptionTimer.currentCount * 10) + " ms]" +
		"\n\t\tinteraction interval (before): " +
			"[" + String(interActionIntervalBefore) +	" ms]" +
		"\n\t\tinteraction interval (after): " +
			"[" + String(interActionIntervalAfter) + " ms]";	
	taskResultStream.writeUTFBytes(taskResultsOutput);
	trace(taskResultsOutput);	
}

/** COMMON UTILITY FUNCTIONS **/

//reset reporting variables and timers for next puzzle
protected function resetPuzzleVars():void
{
	//reset the timers
	taskTimer.stop();
	resumptionTimer.stop();
	scInstructionReadTimer.stop();
	
	taskTimer.reset();
	resumptionTimer.reset();
	scInstructionReadTimer.reset();
	
	//reset number of clicked and moved
	elementsClicked = 0;
	elementsMoved = 0;
	moveAdjustments = 0;
	invalidMoves = 0;
	abortedMoves = 0;	
	
	//reset timed variables
	interruptionTime = 0;
	interruptionDismissalTime = 0;
	interActionIntervalBefore = 0;
	interActionIntervalAfter = 0;
	
	//n-back score
	nBackScore = 0;
	
	//reset inter-action variables
	firstAction = false;
	firstActionTime = 0;
	lastActionTime = 0;
	interActionTotal = 0;
	postInterruption = false;
	completedActions = 0;
	completedActionsSinceInterruption = 0;
}

/** BUTTON CLICK HANDLERS: STATE CHANGING BUTTONS **/

//SC practice button clicked
protected function sc_pracClickHandler(event:Event):void
{	
	resetPuzzleVars();
	
	//set SC practice instruction text
	sc_instructionText = "Move a Star";	
	
	currentState = "sc_practice_puzzle";
	
	//display SC instruction modal window
	var sc_instruction_dialog:SC_Instructions = SC_Instructions(
		PopUpManager.createPopUp(this,SC_Instructions,true) 
		as spark.components.TitleWindow);	
	sc_instruction_dialog.sc_instruction.text=sc_instructionText;
	sc_instruction_dialog.sc_suppl_instruction_text.visible = true;
	sc_instruction_dialog.sc_suppl_instruction_text_2.visible = true;
	sc_instruction_dialog.x = taskContainer.x;
	sc_instruction_dialog.y = taskContainer.y; 
	
	scInstructionReadTimer.start();
	
	//add practice task to frame
	scPracTask = new SCPrac();	
	sc_container.addElementAt(scPracTask,0);
	
	var outputText:String = 
		"\n\n>>> SC practice puzzle: \n\n" + sc_instructionText + "\n";
		
	taskResultStream.writeUTFBytes(outputText);
	trace(outputText);				
}

//SqP practice button clicked
protected function sqp_pracClickHandler(event:MouseEvent):void
{				
	resetPuzzleVars();
	
	//set SqPPrac instruction text
	sqp_instructionText = 
		"You will see line patterns like this one." +
		"Your task is to make complete squares." +
		"\nMove the extra line to cover the pale red line, " +
		"and you have solved this puzzle.";		
	
	currentState = "sqp_practice_puzzle";
		
	//add practice task to frame		
	sqPPracTask = new SqPPrac()
	sqpContainer.addElementAt(sqPPracTask,0);
	
	doneBttn.visible = true;	
	
	var outputText:String = 
		"\n\n>>> SqP practice puzzle: \n\n" + sqp_instructionText + "\n";
	
	taskResultStream.writeUTFBytes(outputText);
	trace(outputText);
	
	mainTaskType = true; //main task == SqP
	//start the task timer
	taskTimer.start(); 
}

//main puzzle set switcher
protected function puzzleSetSwitcher(event:Event, puzzleBank:String):void
{
	resetPuzzleVars(); //reset puzzle variables
		
	var outputText:String;	
	
	//if SC puzzle, switch to specified puzzle bank, else to SqP bank
	if (puzzleBank.search('sc') > -1)
	{		
		SCTimeResultStream.writeUTFBytes("\n");
		if (puzzleBank == "sc_train")
		{
			interruptionCondition = 1;
			MAX_SC_PUZZLE = 2;
			currentState = "sc_train";
		}
		else
		{
			interruptionCondition = scInterruptSeq[scCount];
			MAX_SC_PUZZLE = 9;		
			currentState = scTaskBankOrder[scCount];
		}	
		//output change of puzzle set
		outputText = "\n>>> " + currentState + 
			" puzzle bank; interruption condition: " +
			String(interruptionCondition);
		taskResultStream.writeUTFBytes(outputText);
		trace(outputText);
		nextSCPuzzle();
	}
	else
	{
		SqPTimeResultStream.writeUTFBytes("\n");
		if (puzzleBank == "sqp_train")
		{
			interruptionCondition = 1;
			MAX_SqP_PUZZLE = 2;
			currentState = "sqp_train";
		}
		else
		{
			interruptionCondition = sqpInterruptSeq[sqpCount];
			MAX_SqP_PUZZLE = 7;
			currentState = sqpTaskBankOrder[sqpCount];
		}
		//output change of puzzle set
		outputText = "\n>>> " + currentState + 
			" puzzle bank; interruption condition: " + 
			String(interruptionCondition);
		taskResultStream.writeUTFBytes(outputText);
		trace(outputText);
		mainTaskType = true; //main task == SqP
		nextBttn.visible = true;		
		nextSqPPuzzle();
	}	
}

/** BUTTON CLICK HANDLERS: Continuation buttons **/

//user dismisses the sc_instruction window, begin task timer
public function sc_instruction_closeHandler():void
{
	scInstructionReadTimer.stop();
	
	//report item clicked
	var instructionCloseText:String =
		"\n\tSC instruction read time: " +
		"[" + String(scInstructionReadTimer.currentCount * 10) + " ms]";
	taskResultStream.writeUTFBytes(instructionCloseText);		
	trace(instructionCloseText);
	
	sc_container.visible = true;
	if (currentState == "sc_practice_puzzle")
		doneBttn.visible = true;
	else
		nextBttn.visible = true;
	
	// start the timer for sc task
	taskTimer.start();
	
	// trigger interruption in next task if conditions met
	if (interruptionCondition > 0 && (
		(currentState == "sc_train" && currentPuzzle > 0) ||
		(currentPuzzle == scInterruptTrialSubset[0] ||
		 currentPuzzle == scInterruptTrialSubset[1] ||
		 currentPuzzle == scInterruptTrialSubset[2] ||
		 currentPuzzle == scInterruptTrialSubset[3])
	))
	{	
		//in sc_train set, place a low-demand interruption on trial 2, 
		//and a high-demand interruption on trial 3
		if (currentState == "sc_train" && currentPuzzle == 1)
			interruptionCondition = 1;
		else if (currentState == "sc_train" && currentPuzzle == 2)
			interruptionCondition = 2;
		
		//set interruption to occur after a onset spec. in scInterruptionOnsets
		var interruptOnsetTimer:Timer = 
			new Timer(scInterruptionOnsets[currentPuzzle].time,1);
		
		var interruptionImminent:String =
			"\n\tinterruption to occur in this trial after : " +
			"[" + String(scInterruptionOnsets[currentPuzzle].time) + " ms]";
		taskResultStream.writeUTFBytes(interruptionImminent);		
		trace(interruptionImminent);
		
		//handler for interrupt timer completion
		interruptOnsetTimer.addEventListener(
			TimerEvent.TIMER_COMPLETE,function(event:TimerEvent):void
			{
				interruptPromptHandler();
			});
		interruptOnsetTimer.start();
	}					
}

//user clicks 'done' practice states sc_prac, sqp_prac						
protected function doneBttn_clickHandler(event:MouseEvent):void
{
	taskTimer.stop();
	
	//if instruction not followed in sc practice
	if (currentState == "sc_practice_puzzle" &&
		(elementsMoved != 1 || 
			(scPracTask.yellow_star.x == 150 && 
				scPracTask.yellow_star.y == 300)))
	{
		var SC_Error_OutputText:String = 
			"\n\t\tSC practice puzzle: user did not follow instruction, " +
			"timer reset";
		taskResultStream.writeUTFBytes(SC_Error_OutputText);
		trace(SC_Error_OutputText);
		
		resetPuzzleVars(); //reset puzzle variable
				
		//display alert to user, inform them of their error
		Alert.buttonHeight = 50;
		Alert.buttonWidth = 100; 
		Alert.show('You did not follow the instruction! ' +
			'\nTry again', 'Incorrect', 
			mx.controls.Alert.OK,null, function(event:Event):void
			{
				doneBttn.visible = false;
				//user dismisses Alert, SC instruction window returns
				sc_container.removeElementAt(0);
				sc_container.visible = false;
				sc_pracClickHandler(event);				
			}
		);
	}
		
	//instruction not followed in sqp practice
	else if (currentState == "sqp_practice_puzzle" &&
		(elementsMoved != 1 ||
			(sqPPracTask.vLinePrac.x != 350 || 
				sqPPracTask.vLinePrac.y != 250)))
	{
		var SqP_Error_OutputText:String = 
			"\n\t\tSqP practice puzzle: user did not follow instruction, " +
			"timer reset";
		taskResultStream.writeUTFBytes(SqP_Error_OutputText);
		trace(SqP_Error_OutputText);	
		
		Alert.buttonHeight = 50;
		Alert.buttonWidth = 100; 
		Alert.show('You did not follow the instruction! ' +
			'\nTry again', 'Incorrect', mx.controls.Alert.OK);	
		
		resetPuzzleVars(); //reset puzzle variable
		
		//reset puzzle
		sqPPracTask = new SqPPrac();		
		sqpContainer.removeElementAt(0);
		sqpContainer.addElementAt(sqPPracTask,0);			
		
		//restart the timer
		taskTimer.start();
	}	
	
	//else (no error), return to launch state
	else
	{
		//if successful on sc practice problem, congradulate user
		var comp_prompt:CompletionPrompt = CompletionPrompt(
			PopUpManager.createPopUp(this,CompletionPrompt,true)
			as spark.components.TitleWindow);	
		comp_prompt.x = taskContainer.x;
		comp_prompt.y = taskContainer.y;	
		
		//remove the practice puzzle
		if (currentState == "sqp_practice_puzzle")
			sqpContainer.removeElementAt(0);
		else if (currentState == "sc_practice_puzzle")
		{
			sc_container.removeElementAt(0); 
			sc_container.visible = false;
		}
		doneBttn.visible = false;
		
		//account for clicks (no subsequent move) as aborted move
		abortedMoves += 
			elementsClicked - 
			(elementsMoved + moveAdjustments + abortedMoves + invalidMoves);
		
		taskResultOutputHandler(); //record # of items clicked and moved
		
		resetPuzzleVars();//reset puzzle variable
		
		mainTaskType = false;//reset task type
		
		//return to launch state	
		var completionTimer:Timer = 
			new Timer(1000,1);
		completionTimer.addEventListener(
			TimerEvent.TIMER_COMPLETE,
			function(event:TimerEvent):void
			{
				currentState = "launchState";
			});
		completionTimer.start();
					
	}				
}

//user clicks 'next' in main SC or SqP tasks					
protected function nextBttn_clickHandler(event:MouseEvent):void
{
	taskTimer.stop();
	resumptionTimer.stop();
	
	//if no actions performed, first action is "continue" button
	if (!firstAction)
	{
		firstActionTime = taskTimer.currentCount * 10;
	}
	
	//add to interAction runningtotal, compute inter-action intervals
	//+1 for clicking "Next"
	interActionTotal += ((taskTimer.currentCount * 10) - lastActionTime);
	if (postInterruption)
		interActionIntervalAfter = 
			Math.floor(interActionTotal / (completedActionsSinceInterruption + 1));
	else		
		interActionIntervalBefore = 
			Math.floor(interActionTotal / (completedActions + 1));
			
	//account for clicks (no subsequent move) as aborted move
	abortedMoves += 
		elementsClicked - 
		(elementsMoved + moveAdjustments + abortedMoves + invalidMoves);
	
	//qualitative reporting
	taskResultOutputHandler(); //record # of items clicked and moved
			
	//quantitative reporting
	var quantOutputText:String = "\n" + 
		String(groupID) + "\t" +
		String(subjectID) + "\t" +
		String(currentPuzzle + 1) + "\t" + 
		String(elementsMoved) + "\t" + 
		String(moveAdjustments) + "\t" + 
		String(elementsClicked) + "\t" +
		String(abortedMoves) + "\t" + 
		String(invalidMoves) + "\t" +
		String(interruptionType) + "\t" + 
		String(scInstructionReadTimer.currentCount * 10) + "\t\t" +				
		String(firstActionTime) + "\t\t" +
		String(nBackScore) + "\t\t" + 
		String(interruptionDismissalTime) + "\t\t" +
		String(resumptionTimer.currentCount * 10) + "\t\t" +
		String(interActionIntervalBefore) + "\t\t" +
		String(interActionIntervalAfter) + "\t\t" +
		String(taskTimer.currentCount * 10) + "\t\t\t" +
		String(currentState);
	
	interruptionType = 0;//reset interruption type
	
	//if main task == SqP, write to SqP result stream, else to SC result stream
	if (mainTaskType)	
	{			
		//record quantitative data
		SqPTimeResultStream.writeUTFBytes(quantOutputText);		
		nextSqPPuzzle();//start next SqP puzzle	
	}
	else
	{
		sc_container.visible = false;
		
		//record quantitative data
		SCTimeResultStream.writeUTFBytes(quantOutputText);		
		nextSCPuzzle();//start next SC puzzle	
	}		
}

//begin next puzzle in main SC task banks or return to launchState					
protected function nextSCPuzzle():void
{
	currentPuzzle++;		
	
	resetPuzzleVars(); //reset puzzle variable
	
	//check current puzzle number against max number of puzzle
	if (currentPuzzle <= MAX_SC_PUZZLE)		 
	{	
		//start next SC puzzle & update instruction
		switch (currentState)
		{
			case "sc_a":
				sc_puzzle_stack_a.selectedIndex = currentPuzzle;				
				sc_instructionText = sc_a_inst[currentPuzzle];
				break;
			case "sc_b":
				sc_puzzle_stack_b.selectedIndex = currentPuzzle;			
				sc_instructionText = sc_b_inst[currentPuzzle];
				break;
			case "sc_c":
				sc_puzzle_stack_c.selectedIndex = currentPuzzle;			
				sc_instructionText = sc_c_inst[currentPuzzle];
				break;
			default:
				sc_puzzle_stack_train.selectedIndex = currentPuzzle;			
				sc_instructionText = sc_train_inst[currentPuzzle];
				break;			
		}
		
		//open new SC instruction window
		var sc_instruction_dialog:SC_Instructions = SC_Instructions(
			PopUpManager.createPopUp(this,SC_Instructions,true) 
			as spark.components.TitleWindow);
		sc_instruction_dialog.sc_instruction.text=sc_instructionText;		
		sc_instruction_dialog.x = taskContainer.x;
		sc_instruction_dialog.y = taskContainer.y; 
		scInstructionReadTimer.start();
		
		var nextSCOutputText:String = 
			"\n\n>> " + currentState + " " + String(currentPuzzle + 1) + 
			": \n\n" + sc_instructionText + "\n";
		taskResultStream.writeUTFBytes(nextSCOutputText);
		trace(nextSCOutputText);				
	}
	else
	{		
		//last SC puzzle completed, return to launch state
		currentPuzzle = -1;	
		var finalSCOutputText:String = 
			"\n\n<<< final " + currentState + " puzzle completed";
		taskResultStream.writeUTFBytes(finalSCOutputText);			
		trace(finalSCOutputText);		
		
		var comp_prompt:CompletionPrompt = CompletionPrompt(
			PopUpManager.createPopUp(this,CompletionPrompt,true)
			as spark.components.TitleWindow);	
		comp_prompt.x = taskContainer.x;
		comp_prompt.y = taskContainer.y;
			
		//reset task bank
		switch (currentState)
		{
			case "sc_a":
				sc_puzzle_stack_a.selectedIndex = 0;
				break;
			case "sc_b":
				sc_puzzle_stack_b.selectedIndex = 0;
				break;
			case "sc_c":
				sc_puzzle_stack_c.selectedIndex = 0;
				break;
			default:
				sc_puzzle_stack_train.selectedIndex = 0;
				break;			
		}
		
		//update global counter and progress bar
		if (globalCount < 6 && currentState != "sc_train")
		{			
			globalCount++;
			scCount++;
			if (globalCount == 3)
				sqp_GroupBttns.enabled = true;
			progressBar.setProgress(globalCount,6);
			progressBar.label= "Completed: " + String(globalCount) + " / 6"; 
		}
		//return to launch state	
		var completionTimer:Timer = 
			new Timer(1000,1);		
		completionTimer.addEventListener(
			TimerEvent.TIMER_COMPLETE,
			function(event:TimerEvent):void
			{
				currentState = "launchState";
			});
		completionTimer.start();	
	}	
				
	nextBttn.visible = false;
}

//begin next puzzle in main SC or SqP tasks	or return to launchState				
protected function nextSqPPuzzle():void
{		
	currentPuzzle++;		
	
	resetPuzzleVars(); //reset puzzle variable
	
	//check current puzzle number against max number of puzzle
	if (currentPuzzle <= MAX_SqP_PUZZLE)
	{
		//start next SqP puzzle & update instruction
		switch (currentState)
		{
			case "sqp_a":
				sqp_puzzle_stack_a.selectedIndex = currentPuzzle;				
				sqp_instructionText = sqp_a_inst[currentPuzzle];
				break;
			case "sqp_b":
				sqp_puzzle_stack_b.selectedIndex = currentPuzzle;			
				sqp_instructionText = sqp_b_inst[currentPuzzle];
				break;
			case "sqp_c":
				sqp_puzzle_stack_c.selectedIndex = currentPuzzle;			
				sqp_instructionText = sqp_c_inst[currentPuzzle];
				break;
			default:
				sqp_puzzle_stack_train.selectedIndex = currentPuzzle;			
				sqp_instructionText = sqp_train_inst[currentPuzzle];
				break;			
		}
		
		var nextSqPOutputText:String = 
			"\n\n>> " + currentState + " " + String(currentPuzzle + 1) + ": " + 
			"\n\n" + sqp_instructionText + "\n";
		
		taskResultStream.writeUTFBytes(nextSqPOutputText);
		trace(nextSqPOutputText);
		
		taskTimer.start();
	}
	else
	{		
		//last SqP puzzle completed, return to launch state
		currentPuzzle = -1;		
		
		var finalSqPOutputText:String = 
			"\n\n<<< final " + currentState + " puzzle completed";
			
		taskResultStream.writeUTFBytes(finalSqPOutputText);
		trace(finalSqPOutputText);
		
		var comp_prompt:CompletionPrompt = CompletionPrompt(
			PopUpManager.createPopUp(this,CompletionPrompt,true)
			as spark.components.TitleWindow);	
		comp_prompt.x = taskContainer.x;
		comp_prompt.y = taskContainer.y;		
		
		//reset task bank		
		switch (currentState)
		{
			case "sqp_a":
				sqp_puzzle_stack_a.selectedIndex = 0;
				break;
			case "sqp_b":
				sqp_puzzle_stack_b.selectedIndex = 0;
				break;
			case "sqp_c":
				sqp_puzzle_stack_c.selectedIndex = 0;
				break;
			default:
				sqp_puzzle_stack_train.selectedIndex = 0;
				break;			
		}
		
		//update global counter and progress bar
		if (globalCount < 6 && currentState != "sqp_train")
		{			
			globalCount++;
			sqpCount++;
			if (globalCount == 3)
				sc_GroupBttns.enabled = true;
			progressBar.setProgress(globalCount,6);
			progressBar.label= "Completed: " + String(globalCount) + " / 6"; 
		}
		mainTaskType = false; //main task != SqP
		
		//return to launch state	
		var completionTimer:Timer = 
			new Timer(1000,1);		
		completionTimer.addEventListener(
			TimerEvent.TIMER_COMPLETE,
			function(event:TimerEvent):void
			{
				currentState = "launchState";
			});
		completionTimer.start();			
	}			
}

/** DRAG-DROP HANDLERS **/

//user clicks a shape, so allow drag
public function initiateDrag(e:MouseEvent):void 
{			
	var dragInitiator:Graphic = e.currentTarget as Graphic;
	
	//create a proxy by creating a new copy of the drag source
	var className:String = getQualifiedClassName(dragInitiator);
	var cl:Class = getDefinitionByName(className) as Class;
	var proxy:* = new cl();
	
	//set the proxy's properties to match the drag source
	proxy.width = dragInitiator.width;
	proxy.height = dragInitiator.height;
	proxy.fillColor = (dragInitiator as IDraggableGraphic).fillColor;
	proxy.filters = [new DropShadowFilter()];
	
	//record mouseDown offset from drag source's x and y
	offsetX = e.stageX - e.currentTarget.x;
	offsetY = e.stageY - e.currentTarget.y;
	
	//record the drag source's x and y
	sourceX = e.currentTarget.x;
	sourceY = e.currentTarget.y;	
	
	//report item clicked
	var clickOutputText:String =
		"\n\t[" + String(taskTimer.currentCount * 10) + " ms]: " + 
		IUIComponent(dragInitiator).name + 
		" at (" + String(sourceX) + "," + String(sourceY) + ") clicked";
	taskResultStream.writeUTFBytes(clickOutputText);		
	trace(clickOutputText);
	
	elementsClicked++;
	
	DragManager.doDrag(dragInitiator,null,e,proxy,0,0,.75,true);
}			

//user moves the drag proxy onto the drop target (canvas), so allow drop
public function dragEnterHandler(e:DragEvent):void 
{
	DragManager.acceptDragDrop(e.currentTarget as IUIComponent);
}

//drag-drop handler (valid drop)
public function dragDropHandler(e:DragEvent):void 
{		
	//if first action made in puzzle, save first action time
	if(!firstAction)
	{
		firstActionTime = taskTimer.currentCount * 10;
		firstAction = true;
	}
	
	//if task resumption time running (returning from interruption), stop it now
	if (resumptionTimer.running)
	{
		resumptionTimer.stop();
		
		//compute inter-action interval for before interruption now
		postInterruption = true;		
		//compute inter-action interval
		if (completedActions > 0)
			interActionIntervalBefore = 
				Math.floor(interActionTotal / (completedActions));
		else
			interActionIntervalBefore = 0;			
		
		//reset interAction variables
		interActionTotal = 0;
		lastActionTime = interruptionTime;
		
		//report item clicked		
		var resumptionOutputText:String =
			"\n\t[" + String(taskTimer.currentCount * 10) + " ms]: " + 
			"task resumed; resumption lag time: [" +
			String(resumptionTimer.currentCount * 10) + " ms]";
		taskResultStream.writeUTFBytes(resumptionOutputText);		
		trace(resumptionOutputText);
	}
	
	//add to interAction runningtotal
	interActionTotal += ((taskTimer.currentCount * 10) - lastActionTime);
	lastActionTime = taskTimer.currentCount * 10;
	
	//bring dropped item to front
	e.currentTarget.addElementAt(e.dragInitiator,0);	
	maxDepth++;
	UIComponent(e.dragInitiator).depth = maxDepth;
	
	//adjust drop position for mouse offset
	IUIComponent(e.dragInitiator).x = (e.stageX - offsetX);
	IUIComponent(e.dragInitiator).y = (e.stageY - offsetY);
	
	//snap to nearest 25x on drop
	var numX:Number = IUIComponent(e.dragInitiator).x;
	numX /= 25;
	numX = Math.round(numX);
	numX *= 25;				
	
	//snap to nearest 25y on drop
	var numY:Number = IUIComponent(e.dragInitiator).y;
	numY /= 25;
	numY = Math.round(numY);
	numY *= 25;	
	
	//correct over-edge SC dragging in x
	if (numX < 0)
		numX = 0;
	else if (numX + IUIComponent(e.dragInitiator).width > 1024)
		numX = 1024 - IUIComponent(e.dragInitiator).width;
	
	//correct over-edge SC dragging in y
	if (numY < 0)
		numY = 0;
	else if (numY + IUIComponent(e.dragInitiator).height > 699)
		numY = 699 - IUIComponent(e.dragInitiator).height;	
	
	IUIComponent(e.dragInitiator).x = numX;
	IUIComponent(e.dragInitiator).y = numY;
		
	//check for line conflicts in SsP puzzles
	var lineConflict:Boolean = false;
	
	if (BorderContainer(e.currentTarget).numElements > 0)
	{					
		var i:int = 0;
		
		var elem:IVisualElement;
		var elemName:String;
		var xPos:Number;
		var yPos:Number;
		var elemHeight:Number;
		
		//compare x and y coordinates of all lines in the container
		while (!lineConflict && i < 
			BorderContainer(e.currentTarget).numElements)
		{						
			elem = BorderContainer(e.currentTarget).getElementAt(i);
			elemName = IUIComponent(elem).name;
			xPos = IUIComponent(elem).x;
			yPos = IUIComponent(elem).y;
			elemHeight = IUIComponent(elem).height;			
			
			if ((mainTaskType) && xPos == numX && yPos == numY && 
				IUIComponent(e.dragInitiator).height == elemHeight &&
				IUIComponent(e.dragInitiator).name != elemName)
			{
				//invalid move (line conflict) has occurred
				lineConflict = true;
				invalidMoves++;
				
				var invalidMoveOutputText:String =
					"\n\t[" + String(taskTimer.currentCount * 10) + " ms]: " + 
					"invalid move: " + IUIComponent(e.dragInitiator).name + 
					" cannot be moved from (" + String(sourceX) + "," + 
					String(sourceY) + ") to (" + String(numX) + "," + 
					String(numY) + ") " + "due to a line conflict with " + 
					elemName;				
				taskResultStream.writeUTFBytes(invalidMoveOutputText);
				trace(invalidMoveOutputText);
			}
			i++;
		}					
	}
	
	// if a line conflict occurs, move line back to it original position
	if(lineConflict)
	{
		IUIComponent(e.dragInitiator).x = sourceX;
		IUIComponent(e.dragInitiator).y = sourceY;
	}
	else					
	{		
		
		//check if element was moved or returned to its source location
		if (sourceX == numX && sourceY == numY)
		{
			abortedMoves++;
			//record aborted move
			var abortedMoveOutputText:String = 
				"\n\t[" + String(taskTimer.currentCount * 10) + " ms]: " + 
				"move aborted: " + IUIComponent(e.dragInitiator).name + 
				" remains at (" + String(sourceX) + "," + String(sourceY) 
				+ ")";
			taskResultStream.writeUTFBytes(abortedMoveOutputText);
			trace(abortedMoveOutputText);
		}
		else
		{
			//compute move distance to classify moves and adjustments (50px)
			var absX:Number = Math.abs(numX - sourceX);
			var absY:Number = Math.abs(numY - sourceY);
			var moveDist:Number = Math.floor(
				Math.sqrt(Math.pow(absX,2) + Math.pow(absY,2)));
		
			if (postInterruption)
				completedActionsSinceInterruption++;
			else
				completedActions++;
			//record move event
			var validMoveOutputText:String = 
				"\n\t[" + String(taskTimer.currentCount * 10) + " ms]: " + 
				IUIComponent(e.dragInitiator).name + 
				" moved from (" + String(sourceX) + "," + String(sourceY) + 
				") to (" + String(numX) + "," + String(numY) + ")" +
				" distance: " + String(moveDist) + " px)";
					
			if (moveDist < 50)
			{
				moveAdjustments++;
				taskResultStream.writeUTFBytes(
					validMoveOutputText + " (adjustment)");
				trace(validMoveOutputText + " (adjustment)");
			}		
			else
			{
				elementsMoved++;
				// trigger interruption in next task in sqp if conditions met
				if (mainTaskType && (
					(currentState == "sqp_train" && currentPuzzle > 0) ||
					(interruptionCondition > 0 && 
					(currentPuzzle == sqpInterruptTrialSubset[0] ||
						currentPuzzle == sqpInterruptTrialSubset[1] ||
						currentPuzzle == sqpInterruptTrialSubset[2])
					)))
				{
					//in sqp_train set, place a low-demand interruption on trial 2, 
					//and a high-demand interruption on trial 3
					if (currentState == "sqp_train" && currentPuzzle == 1)
						interruptionCondition = 1;
					else if (currentState == "sqp_train" && currentPuzzle == 2)
						interruptionCondition = 2;
					
					var rand:Number = Math.ceil(Math.random() * 2);
					
					//trigger an interruption if 1 move has been made and
					//rand <=1; or if 2 moves have been made in a 3-move
					//puzzle and an interruption has not yet occurred
					if ((currentPuzzle <= 4 && elementsMoved == 1) ||
						(currentPuzzle > 4 && 
							elementsMoved == 1 && rand <= 1) ||
						(currentPuzzle > 4 && 
							elementsMoved == 2 && !postInterruption))
					{
						//set interruption to occur after 0.5s onset from move
						var interruptOnsetTimer:Timer = 
							new Timer(500,1);
						
						//handler for interrupt timer completion
						interruptOnsetTimer.addEventListener(
							TimerEvent.TIMER_COMPLETE,
							function(event:TimerEvent):void
							{
								interruptPromptHandler();
							});
						interruptOnsetTimer.start();
					}
				}
				taskResultStream.writeUTFBytes(
					validMoveOutputText + " (valid move)");
				trace(validMoveOutputText + " (valid move)");
			}
		}
	}			
}

//drag-drop handler for outside the drop area (invalid drop)
protected function invalidDragDrop(e:DragEvent):void
{	
	invalidMoves++;
	var invalidMoveOutputText:String =
		"\n\t[" + String(taskTimer.currentCount * 10) + " ms]: invalid move: " + 
		IUIComponent(e.dragInitiator).name + 
		" cannot be moved from (" + String(sourceX) + "," + 
		String(sourceY) + ") to outside the drop area";	
	taskResultStream.writeUTFBytes(invalidMoveOutputText);
	trace(invalidMoveOutputText);
}

/** MAIN TASK ORDER CHANGE HANDLLER **/

//handler for changing the main task order (radio button
protected function mainTaskOrderClickHandler(event:Event):void
{
	if (mainTaskOrder)
	{
		mainTaskOrder = false;
		trace("### main task order: SC-SqP");
	}
	else
	{
		mainTaskOrder = true;
		trace("### main task order: SqP-SC");
	}
}

/** INTERRUPTION HANDLERS **/

//handler for changing the interruption condition (drop-down combo box)
protected function interruptStateCB_changeHandler(event:Event):void
{
	//set interruption sequence
	scInterruptSeq[ 0] = ComboBox(event.target).selectedItem.first;
	scInterruptSeq[ 1] = ComboBox(event.target).selectedItem.second;
	scInterruptSeq[ 2] = ComboBox(event.target).selectedItem.third;
	
	sqpInterruptSeq[ 0] = ComboBox(event.target).selectedItem.first;
	sqpInterruptSeq[ 1] = ComboBox(event.target).selectedItem.second;
	sqpInterruptSeq[ 2] = ComboBox(event.target).selectedItem.third;
	
	var outputText:String = 
		"\n### interruption sequence set: " +
		String(interruptStateCB.selectedItem.label);
	trace(outputText);
}

//trigger an interrupt prompt
protected function interruptPromptHandler():void
{	
	//stop the task timer
	taskTimer.stop();
	interruptionTime = taskTimer.currentCount * 10;
	
	//report interruption
	var interruptOutputText:String =
		"\n\t[" + String(taskTimer.currentCount * 10) + " ms]: " +
		"interruption triggered";
	taskResultStream.writeUTFBytes(interruptOutputText);		
	trace(interruptOutputText);
	
	//open interruption modal window, to appear at top of screen
	var interruptPrompt:InterruptionPrompt = 
		InterruptionPrompt(PopUpManager.createPopUp
			(sc_container,InterruptionPrompt,true) 
			as spark.components.TitleWindow);			
	
	interruptPrompt.x = taskContainer.x;
	interruptPrompt.y = taskContainer.y;	
}

//low-complexity interrupt triggered
public function lowInterruptHandler(event:Event):void
{
	interruptionType = 1;//set interruption type to 1 = low
	
	//report interruption
	var interruptOutputText:String =
		"\n\t\ttype: Low-complexity interruption";
	taskResultStream.writeUTFBytes(interruptOutputText);		
	trace(interruptOutputText);
	
	//open low-complexity interruption modal window
	var low_comp_int:InterruptionLow = InterruptionLow(
		PopUpManager.createPopUp(this,InterruptionLow,true)
		as spark.components.TitleWindow);	
	low_comp_int.x = taskContainer.x;
	low_comp_int.y = taskContainer.y;	
}

//high-complexity interrupt triggered
public function highInterruptHandler(event:Event):void
{
	interruptionType = 2;//set interruption type to 2 = high
	
	//report interruption
	var interruptOutputText:String =
		"\n\t\ttype: High-complexity interruption";
	taskResultStream.writeUTFBytes(interruptOutputText);		
	trace(interruptOutputText);
	
	//open high-complexity interruption modal window
	var high_comp_int:InterruptionHigh = InterruptionHigh(
		PopUpManager.createPopUp(this,InterruptionHigh,true)
		as spark.components.TitleWindow);	
	high_comp_int.x = taskContainer.x;
	high_comp_int.y = taskContainer.y;
}