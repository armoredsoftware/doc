--Attestation Agent Main

main = do
  putStrLn "START main of Attestation"
  
  apprChan <- server_init appId
  measChan <- client_init meaId
  
  publicEK <- tpm_key_pubek tpm
  tkShn <- tpm_session_oiap tpm
  tpm_takeownership tpm tkShn publicEK ownerPass srkPass
  putStrLn "\nTPM OWNERSHIP TAKEN\n"

  req <- receiveRequest apprChan
  resp <- mkResponse req
  sendResponse apprChan resp

   where
     ownerPass = tpm_digest_pass oPass
     srkPass = tpm_digest_pass sPass
