'use strict';

/*******************************************************************************/
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
    // "ListLength.hs"     : { "name" : "List Lengths"     , "type" : "measure"},
    // "MapReduce.hs"      : { "name" : "Map Reduce"       , "type" : "measure"}, 
    "KMeansHelper.hs"       : { "name" : "K-Means Lib"      , "type" : "measure"},
    "KMeans.hs"             : { "name" : "K-Means"          , "type" : "measure"}, 
    "TalkingAboutSets.hs"   : { "name" : "Talk About Sets"  , "type" : "measure"},
    "LambdaEval.hs"         : { "name" : "Lambda Eval"      , "type" : "measure"}, 
    "treesum.hs"            : { "name" : "List-Tree Sum"    , "type" : "measure"},
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
/************** Hooking into Codemirror ****************************************/
/*******************************************************************************/

var progArea   = document.getElementById("program");
var progEditor = CodeMirror.fromTextArea(progArea, {
  lineNumbers: true,
  matchBrackets: true,
  mode: "text/x-haskell"
});

var qualArea = document.getElementById("qualifiers");
var qualEditor = CodeMirror.fromTextArea(qualArea, {
  lineNumbers: true,
  matchBrackets: true,
  mode: "text/x-text"
});

qualEditor.setCursor(0, 0); 
//qualEditor.setSize(null, 50); 

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
  $scope.isSafe     = false;
  $scope.isUnsafe   = false;
  $scope.isCrash    = false;
  $scope.isChecking = false;
  $scope.isUnknown  = false;
}

function setStatusUnknown($scope){
  clearStatus($scope);
  $scope.isUnknown = true;
}

function setStatusChecking($scope){
  clearStatus($scope);
  $scope.isChecking = true;
}

function setStatusResult($scope, result){
  clearStatus($scope);
  $scope.isChecking = false;
  $scope.isSafe     = (result == "safe"  );
  $scope.isUnsafe   = (result == "unsafe");
  $scope.isCrash    = (result == "crash" );
  $scope.isUnknown  = !($scope.isSafe || $scope.isUnsafe || $scope.isCrash);
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
    
    $scope.isSafe     = false;
    $scope.isUnsafe   = false;
    $scope.isCrash    = false; 
    $scope.isChecking = false;
    $scope.isUnknown  = true; 

    $scope.msg        = demo.file; 
    $scope.outReady   = false;

    $http.get(srcURL)
      .success(function(src) { progEditor.setValue(src);})
      .error(function(data, stat){ alert("Horrors: No such file!" + srcURL); })
      ;
    $http.get(qualsURL)
      .success(function(quals) { qualEditor.setValue(quals); })
      .error(function(data, stat){ qualEditor.setValue("// No user-specified Qualifiers"); })
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
    var query = { "program"    : progEditor.getValue(), 
                  "qualifiers" : qualEditor.getValue() 
                };

    setStatusChecking($scope);

    $http.post(getVerifierURL(), query)
         .success(function(data, status) {
            $scope.outReady   = true;
            $scope.status     = status;
            globData          = data;
            $scope.result     = data.result;
          
            setStatusResult($scope, data.result);

            // $scope.isChecking = false;
            // $scope.isSafe     = (data.result == "safe"  );
            // $scope.isUnsafe   = (data.result == "unsafe");
            // $scope.isCrash    = (data.result == "crash" );
            // $scope.isUnknown  = !($scope.isSafe || $scope.isUnsafe || $scope.isCrash);
            
            $scope.warns     = data.warns;
            $scope.crash     = data.crash; 
            // $scope.log       = data.log;
            $scope.annotHtml = data.annotHtml;
         })
         .error(function(data, status) {
            var msg = (data || "Request failed") + status;
            alert(msg);
         });
  };
}

