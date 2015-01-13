data TPM_KEY = TPM_KEY {
      tpmKeyUsage   :: TPM_KEY_USAGE
    , tpmKeyFlags   :: TPM_KEY_FLAGS
    , tpmKeyAuth    :: TPM_AUTH_DATA_USAGE
    , tpmKeyParams  :: TPM_KEY_PARMS
    , tpmKeyPcrInfo :: ByteString
    , tpmKeyPublic  :: TPM_STORE_PUBKEY
    , tpmKeyEncData :: ByteString
    } deriving (Eq)

data Session =
  OIAP
  { authHandle :: ByteString
  , nonceEven  :: TPM_NONCE }

  | OSAP
    { authHandle   :: ByteString
    , nonceOddOSAP :: TPM_NONCE
    , nonceEven    :: TPM_NONCE
    , nonceEvenOSAP:: TPM_NONCE
    , secret       :: TPM_DIGEST
    } deriving (Eq)


data TPM_QUOTE_INFO =
  TPM_QUOTE_INFO
  { tpmQuoteInfoCompHash :: TPM_COMPOSITE_HASH
   ,tpmQuoteInfoExData :: TPM_NONCE
    } deriving (Show,Eq)

instance Binary TPM_QUOTE_INFO where
    put (TPM_QUOTE_INFO c d) = do
        put tpm_struct_ver_default
        put tpm_quote_info_fixed
        put c
        put d
    get = do
        t  <- (get :: Get TPM_STRUCT_VER)
        f  <- getLazyByteString (fromIntegral 4)
        c <- get
        d <- get
        return $ TPM_QUOTE_INFO c d
