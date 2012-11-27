'use strict';

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
/************** Top-Level Demo Controller **************************************/
/*******************************************************************************/

function LiquidDemoCtrl($scope, $http) {

  // List of demos
  $scope.basicDemos   = 
     [ { "name" : "Blank"        , "file" : "blank.hs"       } , 
       { "name" : "Test000"      , "file" : "test000.hs"     }
     ];
  $scope.measureDemos = 
    [ { "name" : "List Lengths"  , "file" : "ListLength.hs"  } , 
      { "name" : "Lambda Eval"   , "file" : "LambdaEval.hs"  } , 
      { "name" : "Map Reduce"    , "file" : "MapReduce.hs"   } , 
      { "name" : "KMeans"        , "file" : "KMeans.hs"      }
    ];
  $scope.abstRefDemos = 
    [ { "name" : "List-Sort"     , "file" : "ListSort.hs"    } , 
      { "name" : "BST"           , "file" : "Map.hs"         } , 
      { "name" : "Induction"     , "file" : "Foldr.hs"   }
    ];

  // Load a particular demo
  $scope.loadSource   = function(demo){
    var srcURL      = 'demos/' + demo.file;
    var qualsURL    = 'demos/' + demo.file + '.hquals';
    
    $scope.msg      = demo.file; 
    $scope.outReady = false;

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

  // TODO: call solver, 
  // http://www.cleverweb.nl/javascript/a-simple-search-with-angularjs-and-php/
  $scope.verifySource = function(){ 
    var query = { "program"    : progEditor.getValue(), 
                  "qualifiers" : qualEditor.getValue() 
                };

    $http.post(getVerifierURL(), query)
         .success(function(data, status) {
            $scope.outReady  = true;
            $scope.status    = status;

            $scope.result    = data.result;
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





















