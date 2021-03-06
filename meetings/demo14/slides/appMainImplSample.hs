main = do 
  putStrLn "START main of Appraiser\n"
  (pcrSelect, nonce) <- mkTPMRequest ([0..23]::[Word8])
  let mReq = mkMeasureReq [0..2]
      req = (Request mReq pcrSelect nonce)
  putStrLn $ show req
  putStrLn $ "Press enter to send Request"
  getChar
  chan <- sendRequest req
  putStrLn "\nSENT REQUEST TO ATTESTATION A..."
  putStrLn "\nRECEIVING RESPONSE...\n"
  result <- receiveResponse chan
  case (result) of
	(Left err) ->
          putStrLn "Error getting response..."
	(Right response) -> do
          putStrLn $ "Received: " 
          putStrLn $ show response ++ "\n"
          putStrLn "Evaluating Response: "
          result <- evaluate req response
          showDemoEvalResult result
  
  putStrLn "END main of Appraiser"
