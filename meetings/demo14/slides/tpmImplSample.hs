tpm_loadkey2 :: TPM tpm => tpm -> Session -> TPM_KEY_HANDLE ->
                           PM_KEY -> TPM_DIGEST -> IO TPM_KEY_HANDLE
tpm_loadkey2 tpm (OIAP ah en) parent key pass = do
  on <- nonce_create
  (rtag,size,resl,dat) <- tpm_transmit tpm 45 tag cod (dat on)
  let (handle,dat') = splitAt 4 dat
  return $ decode handle
  where
    tag = tpm_tag_rqu_auth1_command
    cod = tpm_ord_loadkey2
    dat on = concat [ encode parent, encode key, ah, encode on
                    , encode False, encode (ath on) ]
    ath on = tpm_auth_hmac pass en on 0 $ concat [encode cod, encode key]
