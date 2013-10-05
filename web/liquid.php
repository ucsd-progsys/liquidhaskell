<?php

// ini_set('display_errors', 'On');
// error_reporting(E_ALL | E_STRICT);

function execCommand($ths, $dir, $log, $packagedir) {
  $cmd_ld_lib  = 'LANG=en_US.UTF-8 PATH=./:$PATH';
  $cmd_liqhs   = 'LIQUIDHS='.$dir;
  $cmd_packdir = 'GHC_PACKAGE_PATH='.$packagedir.':' ;
  $cmd_liquid  = $dir.'liquid --notermination '.$ths ;
  $cmd         = $cmd_ld_lib.' '.$cmd_liqhs.' '.$cmd_packdir.' '.$cmd_liquid.' > '.$log.' 2>&1';
  return $cmd;
}

function writeFileRaw($fname, $rawstring){
  $f = fopen($fname, "w");
  fwrite($f, $rawstring);
  fclose($f);
}

////////////////////////////////////////////////////////////////////////////////////
//////////////////// Top Level Server //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////


// Get inputs
$data             = file_get_contents("php://input");
$query            = json_decode($data);
$packagedir       = "/home/rjhala/research/liquid/.hsenv_liquid/ghc/lib/ghc-7.6.3/package.conf.d";
$log              = "log";

// echo 'HELLO TO HELL!\n';
// echo ('PGM\n' . $query->program) ;
// echo ('QUALS\n' . $query->qualifiers);

// Generate temporary filenames 
$t                = time();
$ths              = $t   . ".hs";
$thq              = $ths . ".hquals";
$thtml            = $ths . ".html"; 
$tout             = $ths . ".out";  
$terr             = $ths . ".err";
$tjson            = $ths . ".json";

// Write query to files
writeFileRaw($thq, $query->qualifiers);
writeFileRaw($ths, $query->program);

// echo 'wrote files';

// Run solver
$cmd              = execCommand($ths, "./", $log, $packagedir);
writeFileRaw("cmdlog", $cmd);
$res              = shell_exec($cmd);

// Parse results
// $out              = getResultAndWarns($tout) ;
// $out['crash']     = getCrash($log)           ;       

$out              = array(); 
if (file_exists($thtml)){
  $out['annotHtml'] = file_get_contents($thtml);
}

if (file_exists($tjson)){
  $out['annots']    = json_decode(file_get_contents($tjson));
}

// echo 'result = ' . $out['result'];
// echo 'warns = '  . $out['warns'];

// Cleanup temporary files
shell_exec("rm -rf ".$ths."hi");
shell_exec("rm -rf ".$ths."o");
shell_exec("mv ".$t."* saved/");

// Put outputs 
echo json_encode($out);

