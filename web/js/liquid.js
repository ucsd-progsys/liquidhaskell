'use strict';

// Globals
var debugAnnots  = null;
var errorMarkers = [];

/*******************************************************************************r
/************** Extract Demo from URL ******************************************/
/*******************************************************************************/

var allDemos =
  { // Basic Demos
    "blank.hs"              : { "name" : "Blank"            , "type" : "basic"  },
    "refinements101.hs"     : { "name" : "Refinements 101"  , "type" : "basic"  },
    "refinements101reax.hs" : { "name" : "Refinements 102"  , "type" : "basic"  },
    "vectorbounds.hs"       : { "name" : "Vector Bounds"    , "type" : "basic"  },

    // Measure Demos
    "lenMapReduce.hs"       : { "name" : "Safe List"        , "type" : "measure"},
    "KMeansHelper.hs"       : { "name" : "K-Means Lib"      , "type" : "measure"},
    "KMeans.hs"             : { "name" : "K-Means"          , "type" : "measure"}, 
    "TalkingAboutSets.hs"   : { "name" : "Talk About Sets"  , "type" : "measure"},
    "UniqueZipper.hs"       : { "name" : "Unique Zippers"   , "type" : "measure"},
    "LambdaEval.hs"         : { "name" : "Lambda Eval"      , "type" : "measure"}, 
    "treesum.hs"            : { "name" : "List-Tree Sum"    , "type" : "measure"},
    // "ListLength.hs"     : { "name" : "List Lengths"     , "type" : "measure"},
    // "MapReduce.hs"      : { "name" : "Map Reduce"       , "type" : "measure"}, 
    // "ListElts.hs"           : { "name" : "List Elements"    , "type" : "measure"}, 

    // Abstract Refinement Demos
    "absref101.hs"      : { "name" : "Parametric Invariants", "type" : "absref" },  
    "ListSort.hs"       : { "name" : "Sorting Lists"    , "type" : "absref" },
    "Map.hs"            : { "name" : "BinSearch Tree"   , "type" : "absref" },
    "Foldr.hs"          : { "name" : "Induction"        , "type" : "absref" }
  };


function getDemo(name){
  var d = allDemos[name];
  var res = { "name" : d.name , "file" : name };
  return res;
}

function getDemos(ty){ 
  var a = [];
  for (var k in allDemos) { 
    if (allDemos[k].type == ty) 
      a.push(getDemo(k));
  };
  return a;
}

/*******************************************************************************/
/************** Setting Up Editor **********************************************/
/*******************************************************************************/

var progEditor  = ace.edit("program");
progEditor.setTheme("ace/theme/xcode");
var SrcMode     = require("ace/mode/haskell").Mode;
progEditor.getSession().setMode(new SrcMode());
var typeTooltip = new TokenTooltip(progEditor, getAnnot);

function resizeProgEditor() {
  var w = $('#program-pane').width();
  return $('#program').width(w);
};

//listen for changes
$(window).resize(resizeProgEditor);
////set initially
resizeProgEditor();


function resizeQualEditor() {
  var w = $('#qualifier-pane').width();
  return $('#qualifiers').width(w);
};

//listen for changes
$(window).resize(resizeProgEditor);
////set initially
resizeProgEditor();

var qualEditor = ace.edit("qualifiers");
qualEditor.setTheme("ace/theme/xcode");
qualEditor.getSession().setMode(new SrcMode());

/*******************************************************************************/
/** Markers For Errors *********************************************************/
/*******************************************************************************/

function errorRange(err){
  var row0 = err.start.line - 1;
  var col0 = err.start.column - 1;
  var row1 = err.stop.line - 1;
  var col1 = err.stop.column - 1;
  var r    = new Range(row0, col0, row1, col1);
  return r;
}

function errorMarker(editor, err){
  var r = errorRange(err);
  return editor.session.addMarker(r, "ace_step", "error");
}

function errorAceAnnot(err){
  var etext = "Liquid Type Error";
  if (err.text) { etext = err.text; }
  var ann = { row   : err.start.line - 1
            , column: err.start.column
            , text  : etext
            , type  : "error"
            };
  return ann;
}

function setErrors(editor, errs){
  // Add Error Markers
  errorMarkers.forEach(function(m){ editor.session.removeMarker(m); });
  errorMarkers = errs.map(function(e){ return errorMarker(editor, e);});
  
  // Add Gutter Annotations
  editor.session.clearAnnotations();
  var annotations  = errs.map(errorAceAnnot);
  editor.session.setAnnotations(annotations);
}


/*******************************************************************************/
/************** URLS ***********************************************************/
/*******************************************************************************/

function getSrcURL(file)   { return ('demos/' + file);              }
function getQualsURL(file) { return ('demos/' + file + '.hquals');  }
function getVerifierURL()  { return 'liquid.php';                   }

/*******************************************************************************/
/************** Tracking Status ************************************************/
/*******************************************************************************/

function clearStatus($scope){
  $scope.isSafe       = false;
  $scope.isUnsafe     = false;
  $scope.isCrash      = false;
  $scope.isChecking   = false;
  $scope.isUnknown    = true ;
}

function setStatusChecking($scope){
  clearStatus($scope);
  $scope.isChecking = true;
  $scope.isUnknown  = false;
}

var debugResult ;

function setStatusResult($scope, result){
  debugResult = result;

  clearStatus($scope);
  $scope.isChecking   = false;
  $scope.isSafe       = (result == "safe"  );
  $scope.isUnsafe     = (result == "unsafe");
  $scope.isCrash      = (result == "crash" );
  $scope.isUnknown    = !($scope.isSafe || $scope.isUnsafe || $scope.isCrash);
}

/*******************************************************************************/
/************** Top-Level Demo Controller **************************************/
/*******************************************************************************/

var globData = null;

function LiquidDemoCtrl($scope, $http, $location) {

  // Populate list of demos
  $scope.basicDemos   = getDemos("basic")  ;  
  $scope.measureDemos = getDemos("measure");
  $scope.abstRefDemos = getDemos("absref") ;

  // Load a particular demo
  $scope.loadSource   = function(demo){
    var srcURL        = 'demos/' + demo.file;
    var qualsURL      = 'demos/' + demo.file + '.hquals';
   
    clearStatus($scope);

    // $scope.isSafe     = false;
    // $scope.isUnsafe   = false;
    // $scope.isCrash    = false; 
    // $scope.isChecking = false;
    // $scope.isUnknown  = true; 

    $scope.msg        = demo.file; 
    $scope.outReady   = false;

    progEditor.on("change", function(e){ 
      $scope.$apply(function(){
        clearStatus($scope);
      });
    });

    $http.get(srcURL)
      .success(function(src) { progEditor.getSession().setValue(src);})
      .error(function(data, stat){ alert("Horrors: No such file!" + srcURL); })
      ;
    $http.get(qualsURL)
      .success(function(quals) { qualEditor.getSession().setValue(quals); })
      .error(function(data, stat){ qualEditor.getSession().setValue("// No user-specified Qualifiers"); })
      ; 
  };

  // Initialize with Test000.hs
  $scope.loadSource($scope.basicDemos[1]);

  // Extract demo name from URL 
  $scope.$watch('location.search()', function() {
    $scope.demoName = ($location.search()).demo;
    if ($scope.demoName in allDemos) 
      $scope.loadSource(getDemo($scope.demoName));
    }, true);

  // Update demo name in URL 
  $scope.changeTarget = function(demo) {
     $location.search('demo', demo.file);
     $scope.loadSource(demo);
  };

  // http://www.cleverweb.nl/javascript/a-simple-search-with-angularjs-and-php/
  $scope.verifySource = function(){ 
    var query = { "program"    : progEditor.getSession().getValue(), 
                  "qualifiers" : qualEditor.getSession().getValue() 
                };

    setStatusChecking($scope);

    $http.post(getVerifierURL(), query)
         .success(function(data, status) {
           
            //Nuke this: results now viewable in editor pane!
            //$scope.outReady  = true;
            
            $scope.status    = status;
            globData         = data;
            $scope.result    = data.result;
            $scope.warns     = data.warns;
            $scope.crash     = data.crash; 
            $scope.annotHtml = data.annotHtml;
            setStatusResult($scope, data.result);
           
            // This may be "null" if liquid crashed...
            debugAnnots      = data.annots;
            if (data.annots) { 
              setAnnots(data.annots.types);
              setErrors(progEditor, data.annots.errors);
            };
            
        })
         .error(function(data, status) {
            var msg = (data || "Request failed") + status;
            alert(msg);
         });
  };
}

