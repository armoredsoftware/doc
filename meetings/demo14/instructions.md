# ArmoredSoftware Demo Notes - 9 January 2015 - 2:17 PM

## Initiating execution

1. Log into tuna.ittc.ku.edu as alex
1. Log into compute5 as armored, passwd armored
1. Measurer - ssh root@10.100.0.240, passwd armored
	1. cd protoLocal/protocol/measurer/
	1. Make run-relay CLIENT=0 DOMID=3
1. Measurer - ssh root@10.100.0.240, passwd armored
	1. cd protoLocal/protocol/measurer/
	1. make run-hotspot-hackableloop
1. Attestation - ssh root@10.100.0.222, passwd armored
	1. ./Attestation
1. Appraiser - ssh root@10.100.0.234, passwd armored
	1. ./Appraiser

Paul’s CA runs on compute6

## For showing measurement errors:

1. HACK0 in measurer (not relay)
1. Hit enter in attester
1. RESTORE in measurer to restore good values
