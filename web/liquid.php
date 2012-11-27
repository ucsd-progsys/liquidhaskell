<?php

function execCommand($ths, $dir, $log) {
  $cmd_ld_lib = 'LANG=en_US.UTF-8 LD_LIBRARY_PATH='.$dir.'external/z3/lib' ;
  $cmd_liqhs  = 'LIQUIDHS='.$dir;
  $cmd_liquid = $dir.'liquid '.$ths ;
  $cmd        = $cmd_ld_lib.' '.$cmd_liqhs.' '.$cmd_liquid.' > '.$log.' 2>&1';
  return $cmd;
}

function getAnnots($htmlfile){
  $annothtml = "<h3> Annotated Program </h3>" ;
  $annothtml = $annothtml."Hover mouse over variables to see inferred types." ;
  $annothtml = $annothtml.(file_get_contents($htmlfile));
  return $annothtml;
}

function writeFileRaw($fname, $rawstring){
  $f = fopen($fname, "w");
  fwrite($f, $rawstring);
  fclose($f);
}

function getCrash($logfile){ 
  $wflag = 0;
  $crash = "";
  $fh    = fopen($logfile, 'r');

  while (!feof($fh)){
    $s = fgets($fh);
    if (strpos($s, "*** ERROR ***") !== false){
      $wflag    = $wflag + 1;
    } 
    if ($wflag == 3){
      $crash = $crash . $s;
    }
  } 
  fclose($fh);
  return $crash;
}

function getResultAndWarns($outfile){
  $wflag = 0;
  $warns = array();
  $res   = "";

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
      $warns[] = $s;
    }
  } 
  fclose($fh);
  
  if ($failflag == 1){
    $res = "crash";
  } else if ($wflag == 0){
    $res = "safe";
  } else {
    $res = "unsafe";
  }

  return array( "result" => $res
              , "warns"  => $warns ); 
}

////////////////////////////////////////////////////////////////////////////////////
//////////////////// Top Level Server //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////


// Get inputs
$data             = file_get_contents("php://input");
$query            = json_decode($data);

// Generate temporary filenames 
$t                = time();
$ths              = $t   . ".hs";
$thq              = $ths . ".hquals";
$thtml            = $ths . ".html"; 
$tout             = $ths . ".out";  
$terr             = $ths . ".err";
$log              = "log";

// Write query to files
writeFileRaw($thq, $query->qualifiers);
writeFileRaw($ths, $query->program);

// Run solver
$cmd              = execCommand($ths, "./", $log);
$res              = shell_exec($cmd);

// Parse results
$out              = getResultAndWarns($tout);
$out['crash']     = getCrash($log)  ;       
$out['annotHtml'] = getAnnots($thtml)       ;

// Cleanup temporary files
shell_exec("rm -f ".$t."*");

// Put outputs 
echo json_encode($out);

?>
