<?
$logfile = "log";
$flag    = 0;
$wd      = "./";         #"/var/www/liquid/demo/";
$demo    = "tests/test000";

if ($_GET["demo"]){
  $demo = "demo_" . $_GET["demo"];
}

$category = array(
  "blank"        => "tests/blank"
, "test000"      => "tests/test000"
, "list-lengths" => "tests/ListLength"
, "list-sorting" => "tests/ListSort"
, "kmeans"       => "tests/KMeans"
, "lambda-eval"  => "tests/LambdaEval"
, "mapreduce"    => "tests/MapReduce"
, "induction"    => "tests/Foldr"
);

$category = str_replace(" ", " ", $category);

function getWarns($outfile, $logfile){
  $warns    = "";
  $wflag    = 0;
  $failflag = 1;
  $fh = fopen($outfile, 'r');
  while (!feof($fh)){
    $s = fgets($fh);
    if (strpos($s,"Safe") !== false){
      $failflag = 0; 
      $wflag    = 0;
    } 
    if (strpos($s,"Unsafe") !== false){
      $failflag = 0; 
      $wflag    = 1;
    }  
    if ($wflag == 1){
      $warns = $warns . $s;
    }
  } 
  fclose($fh);
  if ($failflag == 1){
    $logurl = "<a href=\"".$logfile."\"> <h3>Log</h3> </a>";
    $warns  = "<h3>Yikes, Crash!: See " . $logurl . "</h3>";
  } else if ($wflag == 0){
    $warns = "<h3>Program Safe</h3>";
  } else {
    $warns = "<h3>Warnings</h3><pre> ".$warns."</pre>";
  }
  return $warns; 
}


function getAnnots($htmlfile){
  $annothtml = "<h3> Annotated Program </h3>" ;
  $annothtml = $annothtml."Hover mouse over variables to see inferred types." ;
  $annothtml = $annothtml.(file_get_contents($htmlfile));
  return $annothtml;
}

function getRawTextFromField($fld){
  return stripslashes($_POST[$fld]);
}

function arrayCat($arr){
  $N = count($arr);
  $res = '';
  for($i=0; $i < $N; $i++){
    $res = $res . " " . $arr[$i];
  }
  return $res;
}

function execCommand($ths, $dir, $log) {
  $cmd_ld_lib = 'LANG=en_US.UTF-8 LD_LIBRARY_PATH='.$dir.'external/z3/lib' ;
  $cmd_liqhs  = 'LIQUIDHS='.$dir;
  $cmd_liquid = $dir.'liquid '.$ths ;
  $cmd        = $cmd_ld_lib.' '.$cmd_liqhs.' '.$cmd_liquid.' > '.$log.' 2>&1';
  return $cmd;
}

function writeFileRaw($fname, $rawstring){
  $f = fopen($fname, "w");
  fwrite($f, $rawstring);
  fclose($f);
}

function writeTextFile($fname, $fld){
  $f = fopen($fname, "w");
  fwrite($f, getRawTextFromField($fld));
  fclose($f);
}

  if($_POST['chooseform'] == "1") {
    $demo = $category[$_POST['choosedemo']]; 
  }

  if($_POST['programform'] == "1") {
    $t     = time();
    $ths   = $t   . ".hs";
    $thq   = $ths . ".hquals";
    $thtml = $ths . ".html"; 
    $tout  = $ths . ".out";  
    $log   = "log";

    writeTextFile($thq, 'qualifiers');
    writeTextFile($ths, 'program');
    $cmd = execCommand($ths, "./", $log);

    writeFileRaw("log", $cmd);
    
    $res       = shell_exec($cmd);
    $annothtml = getAnnots($thtml);
    $warnhtml  = getWarns($tout, $log);
    $loghtml   = "<a href=\"".$log."\"> <h3>Log</h3> </a>".$res;

    $flag       = 1;
    shell_exec("rm -f ".$t."*");
  }
?>

<html>
<head>
  <title>Liquid Haskell Demo</title>
  <link type='text/css' rel='stylesheet' href='syntax/liquid.css' />
  <script src="lib/codemirror.js"></script>
  <link rel="stylesheet" href="lib/codemirror.css">
  <script src="mode/haskell/haskell.js"></script>
</head>
<body>
  <h1>Liquid Haskell Demo</h1>
  <hr />

<h3>Pick a demo</h3>

<form action='<? echo $_SERVER['PHP_SELF']; ?>' 
      method='post'><p>

<select name="choosedemo">
<? foreach ($category as $key => $value){
     if ($value == $demo) { 
       echo '<OPTION selected = "yes" value='.$key.'> '.$key.''; 
     } else{
       echo '<OPTION value='.$key.'> '.$key.''; 
     }
  } 
?>   
</select>
<input name='chooseform' type='hidden' value='1'>
<input type='submit' value='choose'>
<input type='button' value='reset' onclick='window.location = "<? echo $_SERVER['PHP_SELF']; ?>"'>
</form>

<form action='<? echo $_SERVER['PHP_SELF']; ?>' 
      method='post'><p>

<h3>Haskell Source Program</h3>
<textarea id='program' name='program' rows='20' cols='80'>
<?
  if($flag == 1) {
    echo (getRawTextFromField('program'));
  }
  else {
    echo (file_get_contents($demo.".hs"));
  }
?>
</textarea>

<h3>Logical Qualifiers</h3>
<textarea id='qualifiers' name='qualifiers' rows='1' cols='80'>
<?
  if($flag == 1) {
    echo (getRawTextFromField('qualifiers'));
  }
  else {
    echo (file_get_contents($demo.".hs.hquals"));
  }
?>
</textarea>
<br />
<input name='programform' type='hidden' value='1'>
<input type='submit' value='Verify!'>
</p></form>

<hr />
<? echo $warnhtml ?>
<hr />
<? echo $annothtml ?>
<hr />
<? echo $loghtml ?>

  <script>
  var progarea = document.getElementById("program");
  var editor = CodeMirror.fromTextArea(progarea, {
    lineNumbers: true,
    matchBrackets: true,
    mode: "text/x-haskell"
  });

  var qualarea = document.getElementById("qualifiers");
  var qeditor = CodeMirror.fromTextArea(qualarea, {
    lineNumbers: true,
    matchBrackets: true,
    mode: "text/x-text"
  });

  qeditor.setSize(null, 50);

  //qualarea.style.height="50px";
  //document.getElementById("adiv").style.height="100px"
  
  </script>

</body>
</html>
